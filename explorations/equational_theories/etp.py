"""Data of the Equational Theories Project (ETP) as input to an exploration.

The ETP decided every implication between two of its 4694 laws, numbered by
their line in its equations.txt. Three of its files are read here:

- equations.txt, the laws, one per line, with ◇ for the operation
  (https://github.com/teorth/equational_theories/blob/main/data/equations.txt);
- graph.json, the implication graph its website shows: the 4694 x 4694
  outcomes, row the premise and column the conclusion, run-length encoded
  (https://teorth.github.io/equational_theories/implications/graph.json);
- files of finite magmas with one "Table [[...]]" per magma, such as those in
  equational_theories/Generated/All4x4Tables/data, or with an equation number
  before each table, as in data/smallest_magma_examples.txt.

The graph gives every implication with a single premise between laws of the
ETP, which an exploration can take as background implications and then only
ask about implications whose premise has several laws. Its magmas can seed the
expert's pool or the context. The implications it refutes can seed the context
as well, as partial objects known only on the laws the graph decides for them,
which covers refutations by infinite magmas.

Laws that imply each other are interchangeable in an implication, so an
exploration needs only one law of each class of equivalent laws:
`representatives` chooses them, closed under duality, and
`semigroup_representatives` among the right-associated laws, closed under
duality among semigroups.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from math import isqrt
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from explorations.equational_theories.magma import Equation, Magma, Op, Term, Var

GRAPH_URL = "https://teorth.github.io/equational_theories/implications/graph.json"
EQUATIONS_URL = "https://raw.githubusercontent.com/teorth/equational_theories/main/data/equations.txt"

# The outcomes of graph.json, as numbered by the ETP website.
_TRUE = {3, 7}  # explicit and implicit proofs of the implication
_FALSE = {2, 6}  # explicit and implicit proofs of its negation


def _variables_in_order(term: Term, seen: list[str]) -> None:
    if isinstance(term, Var):
        if term.name not in seen:
            seen.append(term.name)
    else:
        _variables_in_order(term.left, seen)
        _variables_in_order(term.right, seen)


def canonical_form(equation: Equation) -> str:
    """The same string for two laws exactly when one becomes the other by
    renaming variables and swapping sides.

    Each side order is written with the variables renamed in the order of
    their first occurrence, and the smaller string is taken.
    """
    forms = []
    for lhs, rhs in ((equation.lhs, equation.rhs), (equation.rhs, equation.lhs)):
        seen: list[str] = []
        _variables_in_order(lhs, seen)
        _variables_in_order(rhs, seen)
        renaming = {name: Var(f"v{k}") for k, name in enumerate(seen)}
        forms.append(f"{lhs.substitute(renaming)} = {rhs.substitute(renaming)}")
    return min(forms)


class EtpLaws:
    """The laws of the ETP, numbered from 1 by their line in equations.txt."""

    def __init__(self, laws: Sequence[Equation]) -> None:
        self.laws = list(laws)
        self._ids = {canonical_form(eq): eq.id for eq in self.laws}

    @classmethod
    def load(cls, path: str | Path) -> EtpLaws:
        lines = Path(path).read_text(encoding="utf-8").splitlines()
        return cls([
            Equation.parse(line.replace("◇", "*"), id=number)
            for number, line in enumerate(lines, start=1)
        ])

    def __len__(self) -> int:
        return len(self.laws)

    def law(self, number: int) -> Equation:
        return self.laws[number - 1]

    def id_of(self, equation: Equation) -> int | None:
        """The number of the ETP law equal to `equation` up to renaming
        variables and swapping sides, or None if the ETP does not list it."""
        return self._ids.get(canonical_form(equation))

    def identify(self, equations: Iterable[Equation]) -> dict[Equation, int]:
        """The ETP number of each of `equations` the ETP lists.

        Raises ValueError if an equation's own id is not the number of the
        law the ETP lists under it.
        """
        numbers = {}
        for eq in equations:
            number = self.id_of(eq)
            if eq.id is not None and eq.id != number:
                listed = f"Eq{number}" if number is not None else "no number"
                raise ValueError(
                    f"{eq} has id {eq.id}, but the ETP lists Eq{eq.id} as "
                    f"{self.law(eq.id) if 1 <= eq.id <= len(self) else 'nothing'} "
                    f"and this law under {listed}"
                )
            if number is not None:
                numbers[eq] = number
        return numbers

    def with_duals(self, numbers: Iterable[int]) -> list[Equation]:
        """The laws with the given numbers and their duals, in the order of
        their numbers."""
        chosen = set()
        for number in numbers:
            chosen.add(number)
            dual = self.id_of(self.law(number).dual())
            if dual is None:
                raise ValueError(f"The ETP does not list the dual of Eq{number}")
            chosen.add(dual)
        return [self.law(number) for number in sorted(chosen)]


class ImplicationGraph:
    """The ETP's decisions about the implications between two of its laws."""

    def __init__(self, outcomes: bytes | bytearray, size: int) -> None:
        if len(outcomes) != size * size:
            raise ValueError(f"{len(outcomes)} outcomes for {size} laws")
        self.outcomes = outcomes
        self.size = size

    @classmethod
    def load(cls, path: str | Path) -> ImplicationGraph:
        """Read graph.json, whose run-length encoding lists each outcome and
        how many times it repeats, row by row."""
        runs = json.loads(Path(path).read_text(encoding="utf-8"))["rle_encoded_array"]
        outcomes = bytearray(sum(runs[1::2]))
        position = 0
        for value, count in zip(runs[::2], runs[1::2]):
            outcomes[position:position + count] = bytes([value]) * count
            position += count
        size = isqrt(len(outcomes))
        return cls(outcomes, size)

    def implies(self, premise: int, conclusion: int) -> bool:
        """Whether law `premise` implies law `conclusion`, by ETP number.

        Raises ValueError if the ETP has not proved the implication or its
        negation.
        """
        outcome = self.outcomes[(premise - 1) * self.size + conclusion - 1]
        if outcome in _TRUE:
            return True
        if outcome in _FALSE:
            return False
        raise ValueError(f"The ETP has not decided whether Eq{premise} implies Eq{conclusion}")

    def equivalence_classes(self, numbers: Iterable[int]) -> list[list[int]]:
        """The classes of the laws with the given numbers that imply each
        other, each sorted, in the order of their smallest numbers."""
        classes: list[list[int]] = []
        for number in sorted(set(numbers)):
            for members in classes:
                if self.implies(number, members[0]) and self.implies(members[0], number):
                    members.append(number)
                    break
            else:
                classes.append([number])
        return classes


def order(equation: Equation) -> int:
    """The number of operations of a law, both sides together."""
    return equation.lhs.op_count() + equation.rhs.op_count()


def representatives(
        laws: EtpLaws,
        classes: Sequence[Sequence[int]],
) -> dict[int, list[int]]:
    """One law of each class of equivalent laws, closed under duality, each
    mapped to the members of its class.

    A class that contains the duals of its laws is represented by its first
    law equal to its own dual, or, if it has none, by its first law and that
    law's dual. Any other class is represented by its first law, and the
    class of its duals by that law's dual. The classes must contain the
    duals of their laws.
    """
    class_of = {number: tuple(members) for members in classes for number in members}

    def dual(number: int) -> int:
        number_of_dual = laws.id_of(laws.law(number).dual())
        if number_of_dual not in class_of:
            raise ValueError(f"The dual of Eq{number} is in none of the classes")
        return number_of_dual

    chosen: dict[int, list[int]] = {}
    for members in classes:
        first = members[0]
        if any(class_of[number] == tuple(members) for number in chosen):
            continue  # represented as the dual of another class
        self_dual = [number for number in members if dual(number) == number]
        if class_of[dual(first)] == tuple(members) and self_dual:
            chosen[self_dual[0]] = list(members)
        else:
            chosen[first] = list(members)
            chosen[dual(first)] = list(class_of[dual(first)])
    return dict(sorted(chosen.items()))


def right_associated(equation: Equation) -> bool:
    """Whether both sides of a law are right-associated, which makes it the
    ETP's form of a law on semigroups."""
    return equation.lhs == equation.lhs.right_associated() and equation.rhs == equation.rhs.right_associated()


def semigroup_representatives(
        laws: EtpLaws,
        classes: Sequence[Sequence[int]],
) -> dict[int, list[int]]:
    """The first law of each class of equivalent right-associated laws, and
    the reversal of each law chosen, each mapped to the members of its class.

    Among semigroups, the dual of a law is the law with both words reversed,
    whose right-associated form is another ETP law, possibly in a class
    whose first law is a different one: it is chosen as well, so that the
    laws chosen are closed under duality. The classes must contain the
    reversals of their laws.
    """
    class_of = {number: list(members) for members in classes for number in members}

    def reversal(number: int) -> int:
        dual = laws.law(number).dual()
        number_of_reversal = laws.id_of(Equation(dual.lhs.right_associated(), dual.rhs.right_associated()))
        if number_of_reversal not in class_of:
            raise ValueError(f"The reversal of Eq{number} is in none of the classes")
        return number_of_reversal

    chosen = {members[0] for members in classes}
    chosen |= {reversal(number) for number in chosen}
    return {number: class_of[number] for number in sorted(chosen)}


def graph_background(
        equations: Sequence[Equation],
        graph: ImplicationGraph,
        laws: EtpLaws,
) -> list[Implication[Equation]]:
    """The implications with at most one premise between `equations` that
    the ETP graph decides, as background implications.

    Each equation the ETP lists implies the others it implies by the graph,
    and the empty premise implies those that x = x implies, which are valid
    in every magma. Equations the ETP does not list take no part.
    """
    numbers = laws.identify(equations)
    listed = [eq for eq in equations if eq in numbers]
    background = []
    trivial = laws.id_of(Equation(Var("x"), Var("x")))
    valid = [eq for eq in listed if graph.implies(trivial, numbers[eq])]
    if valid:
        background.append(Implication((), valid))
    for eq in listed:
        conclusion = [
            other for other in listed
            if other != eq and other not in valid and graph.implies(numbers[eq], numbers[other])
        ]
        if conclusion:
            background.append(Implication([eq], conclusion))
    return background


@dataclass(frozen=True)
class EtpRefutation:
    """A magma, possibly infinite, by which the ETP refutes that law `premise`
    implies law `conclusion`, by ETP number."""

    premise: int
    conclusion: int

    @property
    def name(self) -> str:
        return f"ETP-Eq{self.premise}-not-Eq{self.conclusion}"


def graph_refutations(
        equations: Sequence[Equation],
        graph: ImplicationGraph,
        laws: EtpLaws,
) -> list[PartialObject[EtpRefutation, Equation]]:
    """The implications between two of `equations` that the ETP graph
    refutes, as partial objects.

    The magma refuting that a implies b satisfies a and every law a implies,
    and violates b and every law that implies b; the graph tells nothing else
    about it. Equations the ETP does not list take no part.
    """
    numbers = laws.identify(equations)
    listed = [eq for eq in equations if eq in numbers]
    objects = []
    for a in listed:
        for b in listed:
            if a == b or not _refutes(graph, numbers[a], numbers[b]):
                continue
            objects.append(PartialObject(
                EtpRefutation(numbers[a], numbers[b]),
                {eq for eq in listed if _implies(graph, numbers[a], numbers[eq])},
                {eq for eq in listed if _implies(graph, numbers[eq], numbers[b])},
            ))
    return objects


def _implies(graph: ImplicationGraph, premise: int, conclusion: int) -> bool:
    return premise == conclusion or _decision(graph, premise, conclusion) is True


def _refutes(graph: ImplicationGraph, premise: int, conclusion: int) -> bool:
    return _decision(graph, premise, conclusion) is False


def _decision(graph: ImplicationGraph, premise: int, conclusion: int) -> bool | None:
    try:
        return graph.implies(premise, conclusion)
    except ValueError:
        return None


_TABLE = re.compile(r"\[\s*\[[\d,\s\[\]]*\]\s*\]")


def load_tables(path: str | Path) -> list[Magma]:
    """The magmas of an ETP file of tables, one table such as
    [[0, 1], [1, 0]] per line, after "Table" or an equation number; other
    lines are ignored. A table repeated is read once."""
    magmas = []
    seen = set()
    name = Path(path).stem
    for number, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), start=1):
        match = _TABLE.search(line)
        if match is None:
            continue
        table = tuple(tuple(row) for row in json.loads(match.group()))
        if table in seen:
            continue
        seen.add(table)
        magmas.append(Magma(len(table), table, name=f"{name}:{number}"))
    return magmas


def load_magmas(path: str | Path) -> list[Magma]:
    """Magmas from a JSON file in the format of saved results (.json) or from
    an ETP file of tables (any other suffix)."""
    from explorations.equational_theories.magma import ETP

    if Path(path).suffix == ".json":
        return ETP.load_magmas(path)
    return load_tables(path)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Write ETP laws, closed under duality, as an equations file for "
            "explore.py: the laws with the given numbers, or with --max-order "
            "one law of each class of equivalent laws of at most that order."
        )
    )
    parser.add_argument("etp_equations", type=Path, metavar="EQUATIONS_TXT",
                        help=f"the ETP's equations.txt ({EQUATIONS_URL})")
    parser.add_argument("numbers", type=int, nargs="*", metavar="N",
                        help="ETP numbers of the laws; their duals are added")
    parser.add_argument("--max-order", type=int, metavar="K",
                        help="choose representatives of the laws of at most K operations; needs --graph")
    parser.add_argument("--max-variables", type=int, metavar="V",
                        help="with --max-order, only the laws of at most V variables")
    parser.add_argument("--graph", type=Path, metavar="PATH",
                        help=f"the ETP's graph.json ({GRAPH_URL})")
    parser.add_argument("--semigroup", action="store_true",
                        help="with --max-order, choose among the right-associated laws, the laws on semigroups, "
                             "closed under reversing words, and add associativity (Eq4512)")
    parser.add_argument("-o", "--output", type=Path, metavar="PATH",
                        help="where to write the equations (default: standard output)")
    args = parser.parse_args(argv)
    if (args.max_order is None) == (not args.numbers):
        parser.error("give either law numbers or --max-order")
    if (args.max_order is None) != (args.graph is None):
        parser.error("--max-order and --graph go together")
    if args.semigroup and args.max_order is None:
        parser.error("--semigroup needs --max-order")
    if args.max_variables is not None and args.max_order is None:
        parser.error("--max-variables needs --max-order")
    laws = EtpLaws.load(args.etp_equations)
    if args.max_order is None:
        entries = [{"id": eq.id, "equation": f"{eq.lhs} = {eq.rhs}"} for eq in laws.with_duals(args.numbers)]
    else:
        graph = ImplicationGraph.load(args.graph)
        numbers = [eq.id for eq in laws.laws if order(eq) <= args.max_order
                   and (args.max_variables is None or len(eq.variables) <= args.max_variables)]
        if args.semigroup:
            numbers = [n for n in numbers if right_associated(laws.law(n))]
        classes = graph.equivalence_classes(numbers)
        if args.semigroup:
            chosen = semigroup_representatives(laws, classes)
            associativity = laws.id_of(Equation.parse("x * (y * z) = (x * y) * z"))
            chosen[associativity] = [associativity]
        else:
            chosen = representatives(laws, classes)
        entries = [
            {"id": number, "equation": f"{laws.law(number).lhs} = {laws.law(number).rhs}", "class": members}
            for number, members in chosen.items()
        ]
        print(f"{len(numbers)} laws, {len(classes)} classes, {len(chosen)} representatives", file=sys.stderr)
    text = "[\n" + ",\n".join("  " + json.dumps(entry, ensure_ascii=False) for entry in entries) + "\n]\n"
    if args.output is None:
        sys.stdout.write(text)
    else:
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
