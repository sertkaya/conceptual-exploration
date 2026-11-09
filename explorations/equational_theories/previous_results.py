"""Collect what earlier explorations established, for an exploration of new laws.

usage: previous_results.py NEW_EQUATIONS --etp-equations EQUATIONS_TXT --graph GRAPH_JSON
           [--results DIR=EQUATIONS ...] [--proofs DIR=EQUATIONS ...] [--logs LOG ...] -o OUTPUT_DIR

Each law of an earlier exploration is matched to the ETP law it is, whatever
its variables, and through the ETP graph to the law of NEW_EQUATIONS that is
equivalent to it, if there is one. OUTPUT_DIR then receives:

- magmas.txt, for --seed-context: the finite magmas of the results
  (magmas.json, special_magmas.txt) and of the logs, with their duals, one for
  each row on the new laws that is not the intersection of other rows, so
  that the context has the same closed sets as with all of them;
- free_magmas.json, for --seed-free-magmas: the free magmas of the results and
  of the logs, known to satisfy the new laws that a law they satisfy implies,
  and to violate those that imply a law they violate, by the ETP graph; the
  exploration identifies a free magma by its premise, so the entries with the
  same premise are merged into one;
- background.json, for --background: the implications that earlier
  explorations proved for all magmas (in --proofs results the sources
  confirmed and background; in logs whose expert is Vampire and that assume
  no axioms, the answers Confirmed and the laws an Unconfirmed answer
  proved), with their duals, wherever every law of the premise has an
  equivalent among the new laws. The source mapped is not taken: results
  written before duals of unconfirmed implications were labelled mapped
  unconfirmed give that label to them as well, and the duals of the proved
  implications are added anyway.

Implications found under axioms such as associativity, or by the Z3 expert,
which only searches magmas up to a size, are not proofs; such results belong
to --results, not --proofs.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import sys
from collections.abc import Iterable, Sequence
from pathlib import Path

import numpy as np

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.etp import _TRUE, EtpLaws, ImplicationGraph, load_tables
from explorations.equational_theories.magma import ETP, Equation, Term, Var

Table = tuple[tuple[int, ...], ...]


def transpose(table: Table) -> Table:
    return tuple(zip(*table))


def _value(term: Term, table: np.ndarray, env: dict[str, np.ndarray]) -> np.ndarray:
    if isinstance(term, Var):
        return env[term.name]
    return table[_value(term.left, table, env), _value(term.right, table, env)]


def holds(equation: Equation, table: np.ndarray) -> bool:
    """Whether the magma of the table satisfies the law, for all values of
    its variables at once."""
    variables = equation.variables
    n = len(table)
    grids = np.meshgrid(*[np.arange(n)] * len(variables), indexing="ij") if variables else []
    env = {v: g.ravel() for v, g in zip(variables, grids)}
    size = n ** len(variables)
    left = np.broadcast_to(_value(equation.lhs, table, env), size)
    right = np.broadcast_to(_value(equation.rhs, table, env), size)
    return bool(np.array_equal(left, right))


def irreducible(rows: Sequence[int], width: int) -> list[int]:
    """The positions of the rows, sets of laws as bit masks, that are not the
    intersection of the rows strictly containing them; dropping the others
    leaves the closed sets of the context unchanged."""
    words = (width + 63) // 64
    matrix = np.array([[(r >> (64 * w)) & 0xFFFFFFFFFFFFFFFF for w in range(words)] for r in rows], dtype=np.uint64)
    kept = []
    for k, row in enumerate(matrix):
        supersets = np.all((matrix & row) == row, axis=1)
        supersets[k] = False
        supersets &= np.any(matrix != row, axis=1)
        if not supersets.any() or not np.array_equal(np.bitwise_and.reduce(matrix[supersets]), row):
            kept.append(k)
    return kept


class Matcher:
    """Matches laws to the new laws equivalent to them, by the ETP graph."""

    def __init__(self, new_equations: Sequence[Equation], etp_laws: EtpLaws, graph: ImplicationGraph) -> None:
        self.etp = etp_laws
        n = graph.size
        outcomes = np.frombuffer(bytes(graph.outcomes), dtype=np.uint8).reshape(n, n)
        self.implies = np.isin(outcomes, list(_TRUE))
        numbers = etp_laws.identify(new_equations)
        missing = [eq for eq in new_equations if eq not in numbers]
        if missing:
            raise ValueError(f"New laws not among the ETP's: {missing[:3]}")
        self.new = list(new_equations)
        self.columns = np.array([numbers[eq] - 1 for eq in self.new])
        # The new law equivalent to each ETP law, if any.
        equivalent = self.implies[:, self.columns] & self.implies[self.columns, :].T
        self.match = {m + 1: self.new[int(np.argmax(row))] for m, row in enumerate(equivalent) if row.any()}

    def number(self, equation: Equation) -> int | None:
        return self.etp.id_of(equation)

    def new_law(self, equation: Equation) -> Equation | None:
        number = self.number(equation)
        return None if number is None else self.match.get(number)

    def dual(self, equation: Equation) -> Equation | None:
        return self.new_law(equation.dual())

    def known(self, positive: Iterable[Equation], negative: Iterable[Equation]) -> tuple[set, set]:
        """The new laws that a positive law implies, and those that imply a
        negative law."""
        holds_ = [n - 1 for n in map(self.number, positive) if n is not None]
        fails = [n - 1 for n in map(self.number, negative) if n is not None]
        pos = self.implies[np.ix_(holds_, self.columns)].any(axis=0) if holds_ else np.zeros(len(self.new), bool)
        neg = self.implies[np.ix_(self.columns, fails)].any(axis=1) if fails else np.zeros(len(self.new), bool)
        if (pos & neg).any():
            raise ValueError("A free magma would both satisfy and violate a law")
        return {eq for eq, p in zip(self.new, pos) if p}, {eq for eq, q in zip(self.new, neg) if q}


def _laws(path: Path) -> dict:
    ident = lambda eq: eq.id if eq.id is not None else eq.name or f"{eq.lhs} = {eq.rhs}"
    return {ident(eq): eq for eq in ETP.load_equations(path)}


class Log:
    """The laws, answers and objects in the log of an exploration."""

    def __init__(self, path: Path) -> None:
        self.lines = path.read_text(encoding="utf-8").split("\n")
        header = self.lines[:next(k for k, l in enumerate(self.lines) if l.startswith("Question 1:"))]
        self.laws = {int(m.group(1)): Equation.parse(m.group(2), id=int(m.group(1)))
                     for m in (re.match(r"  - Eq(\d+): (.*)$", l) for l in header) if m}
        expert = next((l for l in header if l.startswith("Expert:")), "")
        self.proofs = "Vampire" in expert and not any(l.startswith("Assumed in Every Object") for l in header)

    def _ids(self, text: str) -> list[Equation]:
        return [self.laws[int(n)] for n in re.findall(r"Eq(\d+):", text)]

    def implications(self) -> Iterable[tuple[list[Equation], list[Equation]]]:
        for k, line in enumerate(self.lines):
            if not re.match(r"Question \d+: ", line) or " -> " not in line:
                continue
            premise, conclusion = line.split(" -> ", 1)
            answer = self.lines[k + 1]
            if answer == "Confirmed":
                yield self._ids(premise.split(": ", 1)[1]), self._ids(conclusion)
            elif answer.startswith("Unconfirmed; proved") or answer.startswith("Open; proved"):
                yield self._ids(premise.split(": ", 1)[1]), self._ids(answer)

    def tables(self) -> Iterable[Table]:
        for k, line in enumerate(self.lines):
            m = re.match(r"Counterexample found: Magma .*\(size (\d+)\)", line)
            if m:
                n = int(m.group(1))
                yield tuple(tuple(map(int, self.lines[k + 3 + i].split("|")[1].split())) for i in range(n))

    def free_magmas(self) -> Iterable[tuple[list[Equation], list[Equation], list[Equation]]]:
        for k, line in enumerate(self.lines):
            m = re.match(r"Counterexample found: Free magma over \{(.*)\}", line)
            if m:
                after = self.lines[k + 1:k + 6]
                sat = next((l for l in after if l.startswith("Satisfies:")), "")
                nsat = next((l for l in after if l.startswith("Does not satisfy:")), "")
                premise = [self.laws[int(n)] for n in re.findall(r"Eq(\d+)", m.group(1))]
                yield premise, self._ids(sat), self._ids(nsat)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Collect the magmas, free magmas and proved implications of earlier explorations "
                    "for an exploration of new laws."
    )
    parser.add_argument("equations", type=Path, metavar="NEW_EQUATIONS", help="the laws of the new exploration")
    parser.add_argument("--etp-equations", type=Path, required=True, metavar="EQUATIONS_TXT")
    parser.add_argument("--graph", type=Path, required=True, metavar="GRAPH_JSON")
    parser.add_argument("--results", nargs="*", default=[], metavar="DIR=EQUATIONS",
                        help="results whose magmas and free magmas to take, with the laws they explored")
    parser.add_argument("--proofs", nargs="*", default=[], metavar="DIR=EQUATIONS",
                        help="results whose implications are proofs over all magmas, with their laws")
    parser.add_argument("--logs", type=Path, nargs="*", default=[], metavar="LOG",
                        help="logs of explorations, possibly unfinished, whose magmas and proofs to take")
    parser.add_argument("-o", "--output", type=Path, required=True, metavar="OUTPUT_DIR")
    args = parser.parse_args(argv)

    new = ETP.load_equations(args.equations)
    matcher = Matcher(new, EtpLaws.load(args.etp_equations), ImplicationGraph.load(args.graph))
    logs = [Log(path) for path in args.logs]
    pair = lambda spec: tuple(map(Path, spec.split("=", 1)))

    # Finite magmas, with their duals.
    tables: dict[Table, str] = {}
    def add(table: Table, source: str) -> None:
        for t in (table, transpose(table)):
            tables.setdefault(t, source)
    for directory, _ in map(pair, args.results):
        if (directory / "magmas.json").exists():
            for m in json.loads((directory / "magmas.json").read_text(encoding="utf-8")):
                add(tuple(map(tuple, m["table"])), directory.name)
        if (directory / "special_magmas.txt").exists():
            for m in load_tables(directory / "special_magmas.txt"):
                add(m.table, directory.name)
    for path, log in zip(args.logs, logs):
        for table in log.tables():
            add(table, path.name)
    rows: dict[int, Table] = {}
    for table in tables:
        array = np.array(table)
        row = sum(1 << k for k, eq in enumerate(new) if holds(eq, array))
        rows.setdefault(row, table)
    order = list(rows)
    kept = [order[k] for k in irreducible(order, len(new))]
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "magmas.txt").write_text(
        "".join(f"Table {json.dumps([list(r) for r in rows[row]])}\n" for row in kept), encoding="utf-8")
    print(f"{len(tables)} finite magmas with their duals, {len(rows)} distinct rows on the "
          f"{len(new)} laws, {len(kept)} of them not intersections of others: magmas.txt")

    # Free magmas. The exploration identifies a free magma by its premise, so
    # entries with the same premise, which are the same magma, are merged.
    free: dict[tuple[str, ...], tuple[set, set]] = {}
    def add_free(premise, positive, negative) -> None:
        pos, neg = matcher.known(positive, negative)
        key = tuple(sorted(f"{eq.lhs} = {eq.rhs}" for eq in premise))
        known_pos, known_neg = free.setdefault(key, (set(), set()))
        known_pos |= {e.id for e in pos}
        known_neg |= {e.id for e in neg}
        if known_pos & known_neg:
            raise ValueError(f"The free magma over {key} would both satisfy and violate a law")
    for directory, equations in map(pair, args.results):
        if (directory / "free_magmas.json").exists():
            laws = _laws(equations)
            for m in json.loads((directory / "free_magmas.json").read_text(encoding="utf-8")):
                premise = [laws[n] for n in m["premise"]]
                if m.get("dual_of") and not set(m["premise"]) <= set(m["positive"]):
                    # Results written before the fix give a dual its original's premise.
                    premise = [eq.dual() for eq in premise]
                add_free(premise, [laws[n] for n in m["positive"]], [laws[n] for n in m["negative"]])
    for log in logs:
        for premise, positive, negative in log.free_magmas():
            add_free(premise, positive, negative)
    entries = [{"premise": list(key), "positive": sorted(pos), "negative": sorted(neg)}
               for key, (pos, neg) in free.items() if neg]
    (args.output / "free_magmas.json").write_text(
        "[\n" + ",\n".join("  " + json.dumps(f) for f in entries) + "\n]\n", encoding="utf-8")
    print(f"{len(entries)} free magmas with distinct premises known to violate one of the laws: free_magmas.json")

    # Proved implications, with their duals.
    proved: list[tuple[list[Equation], list[Equation]]] = []
    for directory, equations in map(pair, args.proofs):
        laws = _laws(equations)
        for i in json.loads((directory / "implications.json").read_text(encoding="utf-8")):
            if i["source"] in ("confirmed", "background"):
                proved.append(([laws[n] for n in i["premise"]], [laws[n] for n in i["conclusion"]]))
    for path, log in zip(args.logs, logs):
        if log.proofs:
            proved += log.implications()
        else:
            print(f"Implications of {path} not taken: its expert is not Vampire, or it assumes axioms.")
    background: dict[frozenset, set] = {}
    for premise, conclusion in proved:
        for match in (matcher.new_law, matcher.dual):
            p = [match(eq) for eq in premise]
            if any(eq is None for eq in p):
                continue
            c = {match(eq) for eq in conclusion} - {None} - set(p)
            if c:
                background.setdefault(frozenset(e.id for e in p), set()).update(e.id for e in c)
    entries = [{"premise": sorted(p), "conclusion": sorted(c)} for p, c in background.items()]
    (args.output / "background.json").write_text(
        "[\n" + ",\n".join("  " + json.dumps(e) for e in entries) + "\n]\n", encoding="utf-8")
    print(f"{len(proved)} proved implications, {len(entries)} premises among the new laws: background.json")


if __name__ == "__main__":
    main()
