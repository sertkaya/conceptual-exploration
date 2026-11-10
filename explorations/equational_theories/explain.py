"""Explain why an implication between laws follows from an exploration's results.

usage: explain.py RESULTS_DIR --equations FILE --premise N ... --conclusion N ...
           [--unconfirmed]

reads the implications an exploration accepted (RESULTS_DIR/implications.json),
finds a minimal set of them that entails premise -> conclusion and a derivation
of it from that set (conceptual_exploration.algorithms.explanation), and prints
the derivation step by step, with the source of each implication. Laws are
given by their id in FILE. Only the implications that hold are used: the
sources background, confirmed and mapped; with --unconfirmed also unconfirmed
and mapped unconfirmed ones, which the derivation marks.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from conceptual_exploration.algorithms.explanation import explain
from conceptual_exploration.core.implication import Implication
from explorations.equational_theories.magma import ETP

PROVED = ("background", "confirmed", "mapped")
UNPROVED = ("unconfirmed", "mapped unconfirmed")


def load_implications(path: Path, sources: Sequence[str]) -> dict[Implication, str]:
    """The implications of an implications.json with the given sources, each
    with its source; one given by several keeps the first in `sources`."""
    found: dict[Implication, str] = {}
    entries = json.loads(path.read_text(encoding="utf-8"))
    for source in sources:
        for entry in entries:
            if entry["source"] == source:
                found.setdefault(Implication(entry["premise"], entry["conclusion"]), source)
    return found


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Explain why an implication between laws follows from an exploration's results."
    )
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR", help="the results of an exploration")
    parser.add_argument("--equations", type=Path, required=True, metavar="FILE", help="the laws it explored")
    parser.add_argument("--premise", nargs="+", required=True, metavar="N", help="ids of the premise laws")
    parser.add_argument("--conclusion", nargs="+", required=True, metavar="N", help="ids of the conclusion laws")
    parser.add_argument("--unconfirmed", action="store_true",
                        help="also use the unconfirmed implications and their images")
    args = parser.parse_args(argv)

    equations = ETP.load_equations(args.equations)
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    by_ident = {str(ident(eq)): ident(eq) for eq in equations}
    text = {ident(eq): f"{eq.lhs} = {eq.rhs}" for eq in equations}
    unknown = [n for n in args.premise + args.conclusion if n not in by_ident]
    if unknown:
        parser.error(f"laws not among the equations: {', '.join(unknown)}")
    premise = [by_ident[n] for n in args.premise]
    conclusion = [by_ident[n] for n in args.conclusion]
    sources = PROVED + (UNPROVED if args.unconfirmed else ())
    implications = load_implications(args.results / "implications.json", sources)

    label = lambda n: f"Eq{n}" if isinstance(n, int) else str(n)
    order = lambda n: (not isinstance(n, int), n if isinstance(n, int) else 0, str(n))
    laws = lambda ns: ", ".join(label(n) for n in sorted(ns, key=order))
    print(f"Explaining {laws(premise)} -> {laws(conclusion)} "
          f"from {len(implications)} implications ({', '.join(sources)}).")
    found = explain(premise, conclusion, list(implications))
    if found is None:
        print("It does not follow from them.")
        sys.exit(1)
    print("\nGiven:")
    for n in sorted(premise, key=order):
        print(f"  {label(n)}: {text[n]}")
    if not found.steps:
        print("\nThe conclusion is part of the premise.")
        return
    # What each step derives that the conclusion or a later step uses.
    used, useful = set(conclusion), []
    for step in reversed(found.steps):
        useful.append(step.derived & used)
        used |= step.implication.premise
    useful.reverse()
    print(f"\nDerivation from a minimal set of {len(found.steps)} of them, "
          f"with the laws each step gives that are used later:")
    for k, (step, gives) in enumerate(zip(found.steps, useful), start=1):
        source = implications[step.implication]
        mark = "  (not proved)" if source in UNPROVED else ""
        rest = len(step.implication.conclusion) - len(gives)
        more = f", and {rest} more" if rest else ""
        print(f"  {k}. {laws(step.implication.premise) or '(nothing)'} -> {laws(gives)}{more}"
              f"   [{source}]{mark}")
        for n in sorted(gives, key=order):
            print(f"       gives {label(n)}: {text[n]}")
    print(f"\nSo {laws(premise)} -> {laws(conclusion)}.")


if __name__ == "__main__":
    main()
