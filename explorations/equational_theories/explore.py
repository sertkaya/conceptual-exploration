"""Conceptual Exploration of Magmas in the Equational Theories Project (ETP).

This script demonstrates how Formal Concept Analysis and Attribute Exploration
can discover the implications between equational laws over magmas
(sets equipped with a single binary operation `*`).

Background:
The Equational Theories Project (ETP) investigates the web of implications
and non-implications between equational laws on magmas.
Using conceptual exploration:
1. The exploration engine proposes candidate implications P => C (premises imply conclusions).
2. The `MagmaExpert` evaluates the implication by checking if all magmas satisfying P also satisfy C.
3. If an implication is false, the expert provides a finite counterexample Magma (with Cayley table).
4. Duality symmetries (the anti-automorphism (x * y)^op = y^op * x^op) are leveraged
   to automatically map implications and reduce expert queries.
5. Queries where the solver runs out of its per-size budget are accepted but
   flagged [UNCONFIRMED], since they were neither refuted nor decided. With
   the Vampire expert, an implication is instead confirmed only when proved,
   counterexamples are searched for at any size, and an implication shown
   false without a counterexample on a particular law is rejected.
6. Optionally, implications derivable by equational reasoning within a bounded
   order are given to the exploration as background knowledge beforehand.
7. The log, the implications found and the context are saved to a results
   directory.
"""

from __future__ import annotations

import argparse
import glob
import json
import shutil
import subprocess
import sys
import tomllib
from collections.abc import Sequence
from datetime import datetime
from pathlib import Path

# Support running directly as a script: add repo root and src to path
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from conceptual_exploration import Implication, Witness, report_every, simplified_rules
from conceptual_exploration.core.context import PartialObject, reduce_objects
from conceptual_exploration.exploration.base import ExplorationBase, ImplicationSource
from conceptual_exploration.exploration.rounds import explore_in_rounds
from explorations.equational_theories.background import background_implications
from explorations.equational_theories.completion import CompletionExpert
from explorations.equational_theories.etp import (
    EtpLaws, EtpRefutation, ImplicationGraph, graph_background, graph_refutations, load_magmas,
)
from explorations.equational_theories.magma import ETP, Equation, Magma, MagmaExpert
from explorations.equational_theories.vampire import FreeMagma, VampireExpert


DEFAULT_EQUATIONS_PATH = Path(__file__).resolve().parent / "equations.json"
RESULTS_PATH = Path(__file__).resolve().parent / "results"
ETP_VERSION = Path(__file__).resolve().parent / "etp_version.json"


class _Tee:
    """Write to several streams at once, to keep a log of what is printed."""

    def __init__(self, *streams):
        self.streams = streams

    def write(self, text: str) -> int:
        for stream in self.streams:
            stream.write(text)
        return len(text)

    def flush(self) -> None:
        for stream in self.streams:
            stream.flush()


def save_results(
    base: ExplorationBase,
    equations: Sequence[Equation],
    directory: Path,
    settings: str,
    refuted: Sequence[Implication[Equation]] = (),
    words: bool = False,
) -> None:
    """Write the implications found and the context of an exploration.

    implications.txt and implications.json list every implication found
    with its source, the rejected implications, and the unconfirmed ones not
    accepted because they would contradict a rejected one;
    simplified_implications.txt lists the implications simplified into
    rules for reading, as printed at the end of the exploration, after the
    background simplified the same way, each followed by its images under
    the symmetries and with its provenance, and with each law written out,
    as a pair of words if `words` (for semigroups); magmas.json holds
    the finite magmas of the context and free_magmas.json the free magmas,
    with their rows, which Vampire may have left partial; etp_refutations.json
    holds the objects standing for refutations of the ETP graph, and
    witnesses.json those standing for implications with one law in their
    conclusion that the expert showed false without a counterexample; context.cxt
    (Burmeister format) holds every object whose row is complete, and
    partial_context.cxt every object, in the same format with ? where it is
    not known whether the object satisfies the equation. A dual image is
    named after its original with ^op.
    """
    directory.mkdir(parents=True, exist_ok=True)
    # Equations are identified by their id, or else by their name or text,
    # and listed in that order.
    position = {eq: k for k, eq in enumerate(equations)}
    # Laws of a free magma's premise may lie outside the equations; they come last.
    order = lambda eq: (eq.id is None, eq.id or 0, position.get(eq, len(position)))
    ordered = sorted(equations, key=order)
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    label = lambda eq: f"Eq{eq.id}" if eq.id is not None else ident(eq)
    ids = lambda eqs: [ident(eq) for eq in sorted(eqs, key=order)]

    numbered = {eq.id: eq for eq in equations if eq.id is not None}

    def law(eq: Equation) -> str:
        sides = "".join(eq.lhs.factors()), "".join(eq.rhs.factors())
        # Associativity itself has the same words on both sides.
        written = f"{sides[0]} = {sides[1]}" if words and sides[0] != sides[1] else f"{eq.lhs} = {eq.rhs}"
        # A law named by its own text is written once.
        return written if label(eq) == written else f"{label(eq)}: {written}"
    laws = lambda eqs: ", ".join(law(eq) for eq in sorted(eqs, key=order)) or "∅"
    # The background, simplified the same way into a cover of its own.
    background = ExplorationBase(attributes=base.attributes, mappings=base.mappings)
    for implication, source in base.implication_sources.items():
        if source is ImplicationSource.BACKGROUND:
            background.accept(implication, ImplicationSource.CONFIRMED)

    # Each rule is followed by its images under the symmetries, other than
    # itself, so that the file lists everything without applying them.
    suffix = lambda j: "^op" if len(base.mappings) == 1 else f"^{j + 1}"
    mapped_source = {
        ImplicationSource.BACKGROUND: "mapped background",
        ImplicationSource.CONFIRMED: "mapped",
        ImplicationSource.UNCONFIRMED: "mapped unconfirmed",
    }

    def listed(rules, tag, source=None):
        seen = set()
        for k, rule in enumerate(rules, start=1):
            own = source or rule.source
            entries = [(f"{tag}{k}", rule.premise, rule.conclusion, own.value if own else "background")]
            # Unconfirmed implications that the base does not map stand for themselves.
            mappings = base.mappings if base.map_unconfirmed or own is not ImplicationSource.UNCONFIRMED else ()
            for j, mapping in enumerate(mappings):
                image = (frozenset(map(mapping, rule.premise)), frozenset(map(mapping, rule.conclusion)))
                if image != (rule.premise, rule.conclusion):
                    entries.append((f"{tag}{k}{suffix(j)}", *image, f"{mapped_source[own]} from [{tag}{k}]"))
            for name, premise, conclusion, provenance in entries:
                text = f"{laws(premise)}  =>  {'everything' if rule.everything else laws(conclusion)}"
                if text not in seen:
                    seen.add(text)
                    yield f"[{name}] {text}   ({provenance})"

    rules = simplified_rules(base)
    background_rules = simplified_rules(background)
    lines = [
        f"The implications found by an exploration ({settings}), simplified for reading, each with "
        "its provenance: premises and conclusions cut to what the symmetries and the other rules do "
        "not give, and the rules then redundant dropped, each rule followed by its images under the "
        "symmetries. The background rules entail the background, and all rules together everything "
        "found.",
        "",
        f"Background ({len(background_rules)} rules and their images):",
        *listed(background_rules, "B", ImplicationSource.BACKGROUND),
        "",
        f"Rules ({len(rules)} rules, as numbered in exploration.log, and their images):",
        *listed(rules, ""),
    ]
    (directory / "simplified_implications.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    def preimage(version, laws):
        # The laws a version satisfies where its original satisfies `laws`:
        # those the mapping sends into them.
        if not version.version:
            return set(laws)
        mapping = base.mappings[version.version - 1]
        return {eq for eq in equations if mapping(eq) in laws}

    names: dict[object, str] = {}
    magmas, free, etp, witnesses, rows = [], [], [], [], []  # rows: (name, positive, negative)
    kind = lambda o: ("F" if isinstance(o, FreeMagma) else "R" if isinstance(o, EtpRefutation)
                      else "W" if isinstance(o, Witness) else "M")
    for version, obj in base.context.objects.items():
        original = version.original
        prefix = kind(original)
        count = sum(1 for o in names if kind(o) == prefix)
        name = names.setdefault(original, f"{prefix}{count + 1}")
        # The only mapping is duality, whose image of a table is its transpose.
        dual_of = name if version.version else None
        if version.version:
            name += "^op"
        rows.append((name, obj.positive, obj.negative))
        if isinstance(original, FreeMagma):
            free.append({
                "name": name, "dual_of": dual_of,
                "premise": ids(preimage(version, original.premise)),
                "positive": ids(obj.positive),
                "negative": ids(obj.negative),
            })
        elif isinstance(original, Witness):
            witnesses.append({
                "name": name, "dual_of": dual_of,
                "refutes": {"premise": ids(preimage(version, original.implication.premise)),
                            "conclusion": ids(preimage(version, original.implication.conclusion))},
                "positive": ids(obj.positive),
                "negative": ids(obj.negative),
            })
        elif isinstance(original, EtpRefutation):
            etp.append({
                "name": name, "dual_of": dual_of,
                "refutes": [
                    next(iter(ids(preimage(version, {numbered[n]})))) if n in numbered else n
                    for n in (original.premise, original.conclusion)
                ],
                "positive": ids(obj.positive),
                "negative": ids(obj.negative),
            })
        else:
            table = tuple(zip(*original.table)) if version.version else original.table
            magmas.append({"name": name, "size": len(table), "table": [list(r) for r in table],
                           "found_as": original.name, "dual_of": dual_of})

    def cell(eq, positive, negative):
        return "X" if eq in positive else "." if eq in negative else "?"

    complete = [row for row in rows if len(row[1]) + len(row[2]) == len(ordered)]
    for filename, objects in (("context.cxt", complete), ("partial_context.cxt", rows)):
        cxt = ["B", "", str(len(objects)), str(len(ordered)), ""]
        cxt += [n for n, _, _ in objects]
        cxt += [label(eq) for eq in ordered]
        cxt += ["".join(cell(eq, pos, neg) for eq in ordered) for _, pos, neg in objects]
        (directory / filename).write_text("\n".join(cxt) + "\n", encoding="utf-8")
    files = ([("magmas.json", magmas), ("free_magmas.json", free)] + ([("etp_refutations.json", etp)] if etp else [])
             + ([("witnesses.json", witnesses)] if witnesses else []))
    for filename, entries in files:
        (directory / filename).write_text(
            "[\n" + ",\n".join("  " + json.dumps(e) for e in entries) + "\n]\n", encoding="utf-8"
        )

    records, lines = [], []
    for idx, implication in enumerate(base.implications, start=1):
        premise = sorted(implication.premise, key=order)
        conclusion = sorted(implication.conclusion, key=order)
        source = base.implication_sources[implication].value
        records.append({"premise": ids(premise), "conclusion": ids(conclusion), "source": source})
        lines.append(
            f"[{idx}] {', '.join(map(label, premise)) or 'Ø'} ==> "
            f"{', '.join(map(label, conclusion))}   ({source})"
        )
    header = [
        f"Implications found by an exploration ({settings}).",
        "background = derived by equational reasoning or taken from the ETP graph; confirmed =",
        "no counterexample in the searched sizes, or proved by Vampire; unconfirmed = neither",
        "refuted nor decided;",
        "mapped = dual of another implication, added when not already entailed; mapped unconfirmed",
        "= dual of an unconfirmed implication. Rejected implications are shown false without a",
        "counterexample known to violate their conclusion; conflicting ones are unconfirmed",
        "implications not accepted because the theory would then entail a rejected one.",
        "",
        "Equations:",
        *(f"  {label(eq)}: {eq.lhs} = {eq.rhs}" for eq in ordered),
        "",
    ]
    for implication in refuted:
        records.append({"premise": ids(implication.premise),
                        "conclusion": ids(implication.conclusion),
                        "source": "refuted"})
    for implication in base.rejected_implications:
        premise = sorted(implication.premise, key=order)
        conclusion = sorted(implication.conclusion, key=order)
        records.append({"premise": ids(premise), "conclusion": ids(conclusion), "source": "rejected"})
    for implication, rejected in base.conflicts:
        records.append({"premise": ids(implication.premise), "conclusion": ids(implication.conclusion),
                        "source": "conflicting",
                        "contradicts": {"premise": ids(rejected.premise), "conclusion": ids(rejected.conclusion)}})
    extra = []
    if refuted:
        extra += ["", "Unconfirmed implications refuted by a later object, and dropped:"]
        extra += [f"  {', '.join(map(label, sorted(i.premise, key=order)))} ==> "
                  f"{', '.join(map(label, sorted(i.conclusion, key=order)))}"
                  for i in refuted]
    show = lambda i: (f"{', '.join(map(label, sorted(i.premise, key=order)))} ==> "
                      f"{', '.join(map(label, sorted(i.conclusion, key=order)))}")
    if base.rejected_implications:
        extra += ["", "Rejected implications:"]
        extra += [f"  {show(i)}" for i in base.rejected_implications]
    if base.conflicts:
        extra += ["", "Unconfirmed implications not accepted, contradicting a rejected one:"]
        extra += [f"  {show(i)}   (contradicts {show(r)})" for i, r in base.conflicts]
    (directory / "implications.txt").write_text(
        "\n".join(header + lines + extra) + "\n", encoding="utf-8"
    )
    (directory / "implications.json").write_text(
        "[\n" + ",\n".join("  " + json.dumps(r) for r in records) + "\n]\n", encoding="utf-8"
    )


def load_free_magmas(path: str | Path, equations: Sequence[Equation]) -> list[PartialObject]:
    """The free magmas of a file in the format of free_magmas.json, as
    objects known on their positive and negative laws."""
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    by_ident = {ident(eq): eq for eq in equations}
    entries = json.loads(Path(path).read_text(encoding="utf-8"))
    unknown = {law for e in entries for law in e["positive"] + e["negative"]} - set(by_ident)
    if unknown:
        raise ValueError(f"Laws of {path} not among the equations: {sorted(map(str, unknown))[:5]}")

    def law(name) -> Equation:
        if name in by_ident:
            return by_ident[name]
        if isinstance(name, str) and "=" in name:
            return Equation.parse(name)
        raise ValueError(f"Law {name!r} of a premise in {path} is neither among the equations nor an equation")

    # A free magma is identified by its premise: entries with the same premise
    # are the same magma, known on what each of them knows.
    known: dict[FreeMagma, tuple[set, set]] = {}
    for e in entries:
        positive, negative = known.setdefault(FreeMagma(frozenset(law(n) for n in e["premise"])), (set(), set()))
        positive |= {by_ident[n] for n in e["positive"]}
        negative |= {by_ident[n] for n in e["negative"]}
    return [PartialObject(free, positive, negative) for free, (positive, negative) in known.items()]


def run_magma_exploration(
    equations_path: str | Path = DEFAULT_EQUATIONS_PATH,
    use_duality_symmetry: bool = True,
    z3_timeout_ms: int | None = None,
    report_interval: int = 20,
    min_search_size: int = 1,
    max_search_size: int = 6,
    background_order: int | None = None,
    background_premise_size: int | None = 2,
    background_transient_order: int | None = None,
    seed_magmas: Sequence[str | Path] = (),
    seed_context: Sequence[str | Path] = (),
    seed_free_magmas: Sequence[str | Path] = (),
    results_dir: str | Path | None = None,
    expert_kind: str = "z3",
    vampire_prove_time_limit: int = 10,
    vampire_first_time_limit: int | None = None,
    vampire_model_time_limit: int = 10,
    vampire_quick_model_time_limit: int = 1,
    vampire_row_time_limit: int | None = None,
    mace4_time_limit: int = 0,
    model_premise: str = "full",
    truncation_words: int = 0,
    eprover_time_limit: int = 0,
    prover9_time_limit: int = 0,
    etp_graph: str | Path | None = None,
    etp_equations: str | Path | None = None,
    etp_refutations: bool = False,
    map_unconfirmed: bool = True,
    axioms: Sequence[int | str] = (),
    background_files: Sequence[str | Path] = (),
):
    if (etp_graph is None) != (etp_equations is None):
        raise ValueError("The ETP graph needs the ETP's equations, and vice versa")
    if etp_refutations and etp_graph is None:
        raise ValueError("The ETP's refutations need the ETP graph")
    row_setting = (
        "" if vampire_row_time_limit is None
        else f", {vampire_row_time_limit} s per other law of a free magma"
    ) + (f", Mace4 {mace4_time_limit} s for models" if mace4_time_limit > 0 else ""
    ) + (f", {model_premise} premises for models" if model_premise != "full" else ""
    ) + (f", truncated free semigroups of up to {truncation_words} words" if truncation_words > 0 else ""
    ) + (f", E {eprover_time_limit} s per law" if eprover_time_limit > 0 else ""
    ) + (f", Prover9 {prover9_time_limit} s per law" if prover9_time_limit > 0 else "")
    first_setting = (
        "" if vampire_first_time_limit is None else f" ({vampire_first_time_limit} s on all cores first)"
    )
    print("=" * 70)
    print("EQUATIONAL THEORIES PROJECT (ETP) — MAGMA EXPLORATION")
    print(f"Equations File:           {Path(equations_path).name}")
    print(f"Duality Symmetry Enabled: {use_duality_symmetry}"
          f"{'' if map_unconfirmed or not use_duality_symmetry else ', duals of unconfirmed implications asked'}")
    if expert_kind == "vampire":
        print(
            f"Expert:                   Vampire, {vampire_prove_time_limit} s to prove{first_setting}, "
            f"{vampire_quick_model_time_limit} s and {vampire_model_time_limit} s for a model"
            f"{row_setting}"
        )
    elif expert_kind == "completion":
        fallback_note = ", Vampire where it fails" if shutil.which("vampire") else ", no fallback"
        print(f"Expert:                   Knuth-Bendix completion{fallback_note}")
    else:
        print(f"Expert:                   Z3, sizes {min_search_size}..{max_search_size}, "
              f"{f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'} per size")
    print(f"Question Reporting:       {f'every {report_interval}' if report_interval >= 1 else 'off'}")
    if background_order is None:
        print("Background Implications:  off")
    else:
        premise_bound = background_premise_size if background_premise_size is not None else "any"
        transient = background_transient_order if background_transient_order is not None else background_order
        print(
            f"Background Implications:  order {background_order}, transient order {transient}, "
            f"premise size {premise_bound}"
        )
    if etp_graph is not None:
        print(f"ETP Implication Graph:    {etp_graph}{', refutations as objects' if etp_refutations else ''}")
    if results_dir is not None:
        print(f"Results Directory:        {results_dir}")
    print("=" * 70)

    equations = ETP.load_equations(equations_path)

    print(f"\nExploring {len(equations)} Equational Laws:")
    for eq in equations:
        print(f"  - {eq}")

    background = []
    if background_order is not None:
        background = background_implications(
            equations, background_order, background_premise_size, background_transient_order
        )
        print(f"\nDerived {len(background)} Background Implications.")
    if etp_graph is not None:
        laws = EtpLaws.load(etp_equations)
        listed = laws.identify(equations)
        graph = ImplicationGraph.load(etp_graph)
        from_graph = graph_background(equations, graph, laws)
        background += from_graph
        print(
            f"\nTook {len(from_graph)} Background Implications from the ETP graph, "
            f"which lists {len(listed)} of the {len(equations)} equations."
        )
    if background_files:
        # Laws are identified as in implications.json: by id, or else by
        # name or text.
        ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
        by_ident = {ident(eq): eq for eq in equations}
        for path in background_files:
            entries = json.loads(Path(path).read_text(encoding="utf-8"))
            unknown = {law for e in entries for law in e["premise"] + e["conclusion"]} - set(by_ident)
            if unknown:
                raise ValueError(f"Laws of {path} not among the equations: {sorted(map(str, unknown))[:5]}")
            given = [
                Implication([by_ident[law] for law in e["premise"]], [by_ident[law] for law in e["conclusion"]])
                for e in entries
            ]
            background += given
            print(f"\nTook {len(given)} Background Implications from {path}.")
    assumed = []
    if axioms:
        # Laws every object satisfies, such as associativity for semigroups.
        ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
        wanted = {int(a) if str(a).isdigit() else a for a in axioms}
        assumed = [eq for eq in equations if ident(eq) in wanted]
        missing = wanted - {ident(eq) for eq in assumed}
        if missing:
            raise ValueError(f"Axioms not among the equations: {sorted(map(str, missing))}")
        background.append(Implication([], assumed))
        print(f"\nAssumed in Every Object:  {', '.join(eq.name or str(eq) for eq in assumed)}")

    # Set up duality mapping if symmetry is enabled; in semigroups, laws are
    # compared up to associativity.
    associativity = Equation.parse("x * (y * z) = (x * y) * z")
    associative = any(eq.is_equivalent_to(associativity) for eq in assumed)
    if truncation_words > 0 and not associative:
        raise ValueError("Truncated free semigroups need associativity among the axioms")
    mappings = []
    if use_duality_symmetry:
        mappings.append(ETP.get_duality_mapping(equations, associative=associative))

    def vampire_expert() -> VampireExpert:
        return VampireExpert(
            attributes=equations,
            prove_time_limit=vampire_prove_time_limit,
            first_time_limit=vampire_first_time_limit,
            model_time_limit=vampire_model_time_limit,
            quick_model_time_limit=vampire_quick_model_time_limit,
            background=background,
            row_time_limit=vampire_row_time_limit,
            mace4_time_limit=mace4_time_limit,
            model_premise=model_premise,
            truncation_words=truncation_words,
            eprover_time_limit=eprover_time_limit,
            prover9_time_limit=prover9_time_limit,
        )

    if expert_kind == "vampire":
        expert = vampire_expert()
    elif expert_kind == "completion":
        if seed_magmas:
            raise ValueError("The completion expert has no pool of magmas to seed")
        expert = CompletionExpert(
            attributes=equations, fallback=vampire_expert() if shutil.which("vampire") else None
        )
    else:
        expert = MagmaExpert(
            attributes=equations,
            min_search_size=min_search_size,
            max_search_size=max_search_size,
            z3_timeout_ms=z3_timeout_ms,
        )
    for path in seed_magmas:
        added = expert.add_magmas(load_magmas(path))
        print(f"Seeded the expert with {added} magmas from {path}.")
    reduced = []
    if seed_context or etp_refutations or seed_free_magmas:
        # Each table once, evaluated on every equation, and the refutations of
        # the ETP graph, reduced to the objects whose rows the others do not
        # already account for.
        tables: dict[tuple, Magma] = {}
        for path in seed_context:
            for magma in load_magmas(path):
                tables.setdefault((magma.size, magma.table), magma)
        if axioms:
            kept = {key: m for key, m in tables.items() if all(m.holds(eq) for eq in assumed)}
            print(f"Dropped {len(tables) - len(kept)} of the {len(tables)} magmas to seed, which violate an axiom.")
            tables = kept
        seeds = [PartialObject(m, *m.evaluate_all(equations)) for m in tables.values()]
        refutations = graph_refutations(equations, graph, laws) if etp_refutations else []
        free = [o for path in seed_free_magmas for o in load_free_magmas(path, equations)]
        reduced = reduce_objects(seeds + refutations + free)
        kept = sum(isinstance(o.object, EtpRefutation) for o in reduced)
        kept_free = sum(isinstance(o.object, FreeMagma) for o in reduced)
        if seed_free_magmas:
            print(f"Seeded the context with {kept_free} of {len(free)} free magmas, the others being redundant.")
        if seed_context:
            print(
                f"Seeded the context with {len(reduced) - kept - kept_free} of {len(seeds)} magmas, "
                f"the others being redundant."
            )
        if etp_refutations:
            print(
                f"Seeded the context with {kept} of the {len(refutations)} refutations "
                f"of the ETP graph, the others being redundant:"
            )
            for o in reduced:
                if isinstance(o.object, EtpRefutation):
                    print(f"  - Eq{o.object.premise} does not imply Eq{o.object.conclusion}")

    def resumed(implication, refuter):
        print(f"\nRefuted the unconfirmed implication {implication} by {getattr(refuter, 'name', refuter)}; "
              f"resuming at its premise.")

    print("\nStarting Attribute Exploration...")
    result = explore_in_rounds(
        equations,
        expert,
        background_implications=background,
        mappings=mappings,
        objects=reduced,
        evaluate_all=True,
        on_question=report_every(report_interval),
        on_resume=resumed,
        map_unconfirmed=map_unconfirmed,
    )
    base, state = result.base, result.state
    state.questions_asked = result.questions_asked
    state.counterexamples = result.counterexamples
    refuted = [(i, getattr(o, "name", str(o))) for i, o in result.refuted]
    rounds = result.rounds

    print("\n" + "=" * 70)
    print("EXPLORATION RESULTS")
    print("=" * 70)
    print(f"Total Questions Asked:        {state.questions_asked}")
    print(f"Accepted Implications:        {len(base.accepted_implications)}")
    print(f"  of which unconfirmed:       {len(base.unconfirmed_implications)}")
    print(f"Implications Found:           {len(base.implications.implications)}")
    print(f"Counterexamples Found:        {len(state.counterexamples)}")
    print(f"Rejected Implications:        {len(base.rejected_implications)}")
    print(f"  Conflicting, Not Accepted:  {len(base.conflicts)}")
    print(f"Rounds:                       {rounds}")
    if isinstance(expert, (VampireExpert, CompletionExpert)):
        answers = ", ".join(f"{kind} {count}" for kind, count in expert.answers.most_common())
        print(f"Expert Answers:               {answers}")

    # Display the implications found, simplified into rules for reading
    rules = simplified_rules(base)
    print(f"\nRules Found (Simplified, {len(rules)} rules):")
    for idx, rule in enumerate(rules, start=1):
        unconfirmed = rule.source is ImplicationSource.UNCONFIRMED
        marker = "   [UNCONFIRMED]" if unconfirmed else ""
        print(f"  [{idx}] {rule.format(lambda eq: eq.name or str(eq))}{marker}")

    if base.unconfirmed_implications and expert_kind in ("vampire", "completion"):
        print(
            "\n  [UNCONFIRMED] = Vampire decided nothing about the implication in time,"
            "\n  so it remains unproved."
            if expert_kind == "vampire" else
            "\n  [UNCONFIRMED] = completion failed and no fallback decided the"
            "\n  implication, so it remains unproved."
        )
    if refuted:
        print("\nUnconfirmed Implications Refuted by a Later Object (and dropped):")
        for implication, name in refuted:
            print(f"  {implication}   (by {name})")
    if base.rejected_implications:
        print("\nRejected Implications (shown false, but no known object violates the conclusion):")
        for implication in base.rejected_implications:
            print(f"  {implication}")
    if base.conflicts:
        print("\nUnconfirmed Implications Not Accepted (they would contradict a rejected one):")
        for implication, rejected in base.conflicts:
            print(f"  {implication}   (contradicts {rejected})")
    if base.unconfirmed_implications and expert_kind == "z3":
        print(
            "\n  [UNCONFIRMED] = no counterexample was found, but the solver ran out"
            "\n  of time at some magma size, so these implications remain unproved rather"
            f"\n  than verified for sizes {expert.min_search_size}..{expert.max_search_size}."
        )

    # Display discovered counterexample magmas
    print("\nSample Counterexample Magmas Generated:")
    unique_magmas = []
    seen = set()
    for cex in state.counterexamples:
        m = cex.object.original if hasattr(cex.object, "original") else cex.object
        if not isinstance(m, Magma):
            continue
        key = (m.size, m.table)
        if key not in seen:
            seen.add(key)
            unique_magmas.append(m)

    for i, m in enumerate(unique_magmas[:5], start=1):
        print(f"\nCounterexample #{i}:")
        print(m)

    if results_dir is not None:
        if expert_kind == "completion":
            expert_settings = "Knuth-Bendix completion expert"
        elif expert_kind == "vampire":
            expert_settings = (
                f"Vampire expert, {vampire_prove_time_limit} s to prove{first_setting}, "
                f"{vampire_quick_model_time_limit} s and {vampire_model_time_limit} s for a model"
                f"{row_setting}"
            )
        else:
            expert_settings = (
                f"search sizes {expert.min_search_size}..{expert.max_search_size}, "
                f"{f'{z3_timeout_ms} ms' if z3_timeout_ms else 'unbounded'} per size"
            )
        settings = f"{Path(equations_path).name}, {state.questions_asked} questions, {expert_settings}"

        if etp_graph is not None:
            settings += ", ETP graph as background"
        if etp_refutations:
            settings += " and its refutations as objects"
        if not map_unconfirmed:
            settings += ", duals of unconfirmed implications asked"
        if background_order is not None:
            settings += (
                f", background order {background_order}, transient order "
                f"{background_transient_order or background_order}, premise size "
                f"{background_premise_size or 'any'}"
            )
        save_results(base, equations, Path(results_dir), settings, [i for i, _ in refuted], words=associative)
        print(f"\nResults saved to {results_dir}.")

    return state, base


def build_parser() -> argparse.ArgumentParser:
    """The command-line options of explore.py."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--config",
        type=Path,
        default=None,
        metavar="FILE",
        help=(
            "A TOML file of options, such as the settings.toml that every run "
            "saves with its results, keyed by option name without the dashes; "
            "options given on the command line override it. Paths are "
            "relative to the directory explore.py is run from, and patterns "
            "such as etp/magmas/*.txt are expanded."
        ),
    )
    parser.add_argument(
        "--equations",
        type=Path,
        default=DEFAULT_EQUATIONS_PATH,
        metavar="PATH",
        help=(
            "JSON file listing the equations to explore as attributes "
            "(default: equations.json next to this script). Each entry has an "
            '"equation" string and optional "name" and "id" fields; the set '
            "must be closed under duality."
        ),
    )
    parser.add_argument(
        "--expert",
        choices=("z3", "vampire", "completion"),
        default="z3",
        help=(
            "How questions are answered (default: z3). z3 searches for "
            "counterexamples of the sizes given below and accepts an implication "
            "when it finds none; vampire tries to prove the implication with the "
            "Vampire theorem prover and searches for a counterexample of any "
            "size, accepting the implication as confirmed only when proved; "
            "completion decides each question by Knuth-Bendix completion of its "
            "premise, refuting it with the free magma over the premise, and "
            "passes the questions whose premise it cannot complete to Vampire "
            "if installed (meant for one-variable laws, where completion succeeds)."
        ),
    )
    parser.add_argument(
        "--vampire-prove-time-limit",
        type=int,
        default=10,
        metavar="S",
        help="Seconds Vampire gets to prove an implication or a single law (default: 10).",
    )
    parser.add_argument(
        "--vampire-first-time-limit",
        type=int,
        default=None,
        metavar="S",
        help=(
            "Seconds Vampire gets, on all cores, for its first attempt at the whole "
            "question (default: the proving time limit; 3 is enough)."
        ),
    )
    parser.add_argument(
        "--vampire-model-time-limit",
        type=int,
        default=10,
        metavar="S",
        help=(
            "Seconds Vampire gets for a second search for a finite "
            "counterexample, made for each law of the conclusion not proved "
            "when the free magma over the premise does not refute the "
            "implication (default: 10)."
        ),
    )
    parser.add_argument(
        "--vampire-quick-model-time-limit",
        type=int,
        default=1,
        metavar="S",
        help=(
            "Seconds Vampire first gets to find a finite counterexample "
            "(default: 1). Failing that, it decides each law separately for "
            "the free magma over the premise, with the proving time limit per "
            "law."
        ),
    )
    parser.add_argument(
        "--vampire-row-time-limit",
        type=int,
        default=None,
        metavar="S",
        help=(
            "Seconds Vampire gets for each law outside the conclusion when it "
            "computes the row of a free magma (default: the proving time "
            "limit); 0 asks only about the laws of the conclusion and leaves "
            "the others unknown."
        ),
    )
    parser.add_argument(
        "--mace4-time-limit",
        type=int,
        default=0,
        metavar="S",
        help=(
            "Seconds the Mace4 model finder gets in all, alongside Vampire's "
            "second search, for finite counterexamples to the laws of the "
            "conclusion not proved, sweeping the sizes on all cores, one law "
            "and one size per search (default: 0, Mace4 not used)."
        ),
    )
    parser.add_argument(
        "--model-premise",
        choices=("full", "simplified", "both"),
        default="full",
        help=(
            "The premise the second search for counterexamples uses: the "
            "question's, a subset whose closure under the background and the "
            "implications proved is the question's, or both (default: full). "
            "A model is checked against the question's premise in any case."
        ),
    )
    parser.add_argument(
        "--truncation-words",
        type=int,
        default=0,
        metavar="W",
        help=(
            "With associativity among the axioms, refute questions with the "
            "truncated free semigroups of the premise's variety, of at most W "
            "words, before the per-law model search (default: 0, not used)."
        ),
    )
    parser.add_argument(
        "--prover9-time-limit",
        type=int,
        default=0,
        metavar="S",
        help=(
            "With the Vampire expert, let Prover9 try to prove each law of the "
            "conclusion that E leaves in the free magma's row, for S seconds, "
            "before Vampire (default: 0, not used)."
        ),
    )
    parser.add_argument(
        "--eprover-time-limit",
        type=int,
        default=0,
        metavar="S",
        help=(
            "Seconds the E prover gets first to decide each law of the "
            "conclusion in a free magma's row, Vampire then getting the laws "
            "it leaves (default: 0, E not used; 2 is enough)."
        ),
    )
    parser.add_argument(
        "--min-search-size",
        type=int,
        default=1,
        metavar="N",
        help=(
            "Smallest magma size the solver searches for counterexamples "
            "(default: 1). The built-in pool of small standard magmas is "
            "still checked first, whatever this is set to."
        ),
    )
    parser.add_argument(
        "--max-search-size",
        type=int,
        default=6,
        metavar="N",
        help=(
            "Largest magma size the solver searches for counterexamples "
            "(default: 6). An implication with no counterexample in the "
            "searched range is accepted, though a larger counterexample "
            "may exist."
        ),
    )
    parser.add_argument(
        "--z3-timeout-ms",
        type=int,
        default=30000,
        metavar="MS",
        help=(
            "Per-magma-size solver budget in milliseconds (default: 30000); "
            "0 or less runs unbounded. A few pathological searches at the "
            "larger magma sizes can dominate the running time, and the budget "
            "cuts those short. Queries that run out of budget are neither "
            "refuted nor decided, and are reported [UNCONFIRMED]."
        ),
    )
    parser.add_argument(
        "--report-every",
        type=int,
        default=1,
        metavar="N",
        help=(
            "Print every Nth question and its outcome while exploring "
            "(default: 1); 0 or less reports nothing. Use 1 to watch every "
            "question the expert is asked."
        ),
    )
    parser.add_argument(
        "--background-order",
        type=int,
        default=None,
        metavar="N",
        help=(
            "Derive background implications with equational reasoning "
            "(multiplying both sides by a term, substituting a term for the "
            "variable, replacing a subterm by an equivalent one) through "
            "equations of at most N operations, at least the largest order "
            "among the explored equations (default: no background "
            "implications). Only one-variable equations are supported."
        ),
    )
    parser.add_argument(
        "--background-premise-size",
        type=int,
        default=2,
        metavar="K",
        help=(
            "Largest premise of a background implication (default: 2); 0 or "
            "less computes the canonical basis of everything derivable, whose "
            "premises may be of any size, at a much higher cost."
        ),
    )
    parser.add_argument(
        "--seed-magmas",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "Files of magmas, such as the magmas.json of earlier results or "
            "ETP files of tables (any suffix but .json), added to the "
            "expert's pool of standard magmas. The pool is checked for a "
            "counterexample before the solver searches for one."
        ),
    )
    parser.add_argument(
        "--seed-free-magmas",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "Files of free magmas, such as the free_magmas.json of earlier "
            "results: JSON lists of objects with a premise and the laws known "
            "to hold (positive) and to fail (negative), given as for "
            "--background; laws of a premise that are not among the equations "
            "may be given by their text. Each is added to the context as an "
            "object known on these laws only, before the exploration starts, "
            "after dropping those whose rows the others account for."
        ),
    )
    parser.add_argument(
        "--seed-context",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "Files of magmas, as for --seed-magmas, evaluated on every "
            "equation and added to the context before the exploration "
            "starts, after dropping those whose rows the others account "
            "for. No question that they refute is asked."
        ),
    )
    parser.add_argument(
        "--background",
        type=Path,
        nargs="+",
        default=[],
        metavar="PATH",
        help=(
            "Files of implications known to hold, given to the exploration as "
            "background implications: JSON lists of objects with a premise "
            "and a conclusion, each a list of laws given by their id, or else "
            "their name or text, as in implications.json."
        ),
    )
    parser.add_argument(
        "--background-transient-order",
        type=int,
        default=None,
        metavar="M",
        help=(
            "Let a single multiplication or substitution reach equations of up "
            "to M operations, provided rewriting with derived equations brings "
            "the result back within --background-order (default: the "
            "background order itself, so no step goes beyond it)."
        ),
    )
    parser.add_argument(
        "--etp-graph",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "The ETP's implication graph (graph.json of its website), whose "
            "implications between two of the equations are given to the "
            "exploration as background implications; needs --etp-equations."
        ),
    )
    parser.add_argument(
        "--axiom",
        nargs="+",
        default=[],
        metavar="LAW",
        help=(
            "Laws every object satisfies, by id or name, such as 4512 "
            "(associativity) to explore semigroups: they are given as a "
            "background implication with an empty premise."
        ),
    )
    parser.add_argument(
        "--no-duality",
        action="store_true",
        help="Do not use the duality symmetry, so that the equations need not be closed under duality.",
    )
    parser.add_argument(
        "--ask-unconfirmed-duals",
        action="store_true",
        help=(
            "Do not add the dual of an unconfirmed implication to the theory "
            "until the implication is confirmed, so that it does not steer the "
            "enumeration; the dual is asked about when the enumeration reaches "
            "it, and if it is proved, the implication is confirmed as well."
        ),
    )
    parser.add_argument(
        "--etp-refutations",
        action="store_true",
        help=(
            "Also add the implications between two of the equations that the "
            "ETP graph refutes to the context, each as an object known to "
            "satisfy its premise and the laws the premise implies and to "
            "violate its conclusion and the laws implying it, whether the "
            "ETP's counterexample is finite or not; needs --etp-graph."
        ),
    )
    parser.add_argument(
        "--etp-equations",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "The ETP's equations.txt, by which the equations are matched with "
            "the ETP's laws whatever their variables and ids; an id that is "
            "not the ETP's number of the law is an error."
        ),
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=None,
        metavar="PATH",
        help=(
            "Directory to save the log, the implications found and the context "
            "in (default: a new directory under results/ named after the "
            "equations file and the starting time). It must not hold results "
            "already."
        ),
    )
    return parser


SEED_OPTIONS = ("seed_magmas", "seed_context", "seed_free_magmas")


def read_config(parser: argparse.ArgumentParser, path: Path) -> dict:
    """The options of a TOML file, as defaults for the parser, converted as
    the command line would convert them."""
    actions = {action.dest: action for action in parser._actions}
    defaults = {}
    for key, value in tomllib.loads(path.read_text(encoding="utf-8")).items():
        dest = key.replace("-", "_")
        action = actions.get(dest)
        if action is None or dest in ("help", "config"):
            parser.error(f"{path}: unknown option {key!r}")
        if action.type is not None:
            value = [action.type(v) for v in value] if isinstance(value, list) else action.type(value)
        if action.choices is not None and value not in action.choices:
            parser.error(f"{path}: {key} must be one of {', '.join(map(str, action.choices))}")
        defaults[dest] = value
    return defaults


def parse_arguments(parser: argparse.ArgumentParser, argv: Sequence[str] | None = None) -> argparse.Namespace:
    """The options of the command line, with those of --config as defaults,
    and the patterns among the seed files expanded."""
    pre = argparse.ArgumentParser(add_help=False)
    pre.add_argument("--config", type=Path, default=None)
    known, _ = pre.parse_known_args(argv)
    if known.config is not None:
        parser.set_defaults(**read_config(parser, known.config))
    args = parser.parse_args(argv)
    for dest in SEED_OPTIONS:
        expanded = []
        for path in getattr(args, dest):
            if any(c in str(path) for c in "*?["):
                matches = sorted(glob.glob(str(path)))
                if not matches:
                    parser.error(f"no files match {path}")
                expanded += map(Path, matches)
            else:
                expanded.append(path)
        setattr(args, dest, expanded)
    return args


def _toml_value(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, (list, tuple)):
        return "[" + ", ".join(_toml_value(v) for v in value) + "]"
    return json.dumps(str(value))


def write_settings(parser: argparse.ArgumentParser, args: argparse.Namespace, path: Path) -> None:
    """Save every option of the run, so that explore.py --config PATH runs it
    again; the results directory is left out, so that a new one is made."""
    root = Path(__file__).resolve().parent.parent.parent
    try:
        commit = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                                capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    etp = json.loads(ETP_VERSION.read_text(encoding="utf-8"))["commit"] if ETP_VERSION.exists() else "unknown"
    lines = [
        "# The options of an exploration, for explore.py --config; paths are",
        "# relative to the directory explore.py was run from.",
        f"# conceptual-exploration commit {commit}; ETP data of commit {etp} (etp_version.json).",
        "",
    ]
    for action in parser._actions:
        if action.dest in ("help", "config", "results_dir"):
            continue
        name = action.option_strings[0].lstrip("-")
        value = getattr(args, action.dest)
        lines.append(f"# {name} not set" if value is None else f"{name} = {_toml_value(value)}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> None:
    parser = build_parser()
    args = parse_arguments(parser, argv)
    if (args.etp_graph is None) != (args.etp_equations is None):
        parser.error("--etp-graph and --etp-equations go together")
    if args.etp_refutations and args.etp_graph is None:
        parser.error("--etp-refutations needs --etp-graph")
    if not 1 <= args.min_search_size <= args.max_search_size:
        parser.error("search sizes must satisfy 1 <= --min-search-size <= --max-search-size")
    results_dir = args.results_dir or (
        RESULTS_PATH / f"{args.equations.stem}_{datetime.now():%Y-%m-%d_%H%M%S}"
    )
    if (results_dir / "exploration.log").exists():
        parser.error(f"{results_dir} already holds results")
    results_dir.mkdir(parents=True, exist_ok=True)
    write_settings(parser, args, results_dir / "settings.toml")
    # Line-buffered, so the log can be followed while the exploration runs.
    with open(results_dir / "exploration.log", "w", encoding="utf-8", buffering=1) as log:
        sys.stdout = _Tee(sys.__stdout__, log)
        try:
            run_magma_exploration(
                equations_path=args.equations,
                use_duality_symmetry=not args.no_duality,
                z3_timeout_ms=args.z3_timeout_ms if args.z3_timeout_ms > 0 else None,
                report_interval=args.report_every,
                min_search_size=args.min_search_size,
                max_search_size=args.max_search_size,
                background_order=args.background_order,
                background_premise_size=(
                    args.background_premise_size if args.background_premise_size > 0 else None
                ),
                background_transient_order=args.background_transient_order,
                seed_magmas=args.seed_magmas,
                seed_context=args.seed_context,
                seed_free_magmas=args.seed_free_magmas,
                results_dir=results_dir,
                expert_kind=args.expert,
                vampire_prove_time_limit=args.vampire_prove_time_limit,
                vampire_first_time_limit=args.vampire_first_time_limit,
                vampire_model_time_limit=args.vampire_model_time_limit,
                vampire_quick_model_time_limit=args.vampire_quick_model_time_limit,
                vampire_row_time_limit=args.vampire_row_time_limit,
                mace4_time_limit=args.mace4_time_limit,
                model_premise=args.model_premise,
                truncation_words=args.truncation_words,
                eprover_time_limit=args.eprover_time_limit,
                prover9_time_limit=args.prover9_time_limit,
                etp_graph=args.etp_graph,
                etp_equations=args.etp_equations,
                etp_refutations=args.etp_refutations,
                map_unconfirmed=not args.ask_unconfirmed_duals,
                axioms=args.axiom,
                background_files=args.background,
            )
        finally:
            sys.stdout = sys.__stdout__


if __name__ == "__main__":
    main()
