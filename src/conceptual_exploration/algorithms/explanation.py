"""Explanations of entailments between implications.

An implication P -> Q follows from a set L of implications when Q lies in the
closure of P under L. An explanation consists of

- a subset K of L that entails P -> Q and is minimal: no proper subset of K
  entails it;
- a derivation of P -> Q from K: a sequence of steps, each applying an
  implication of K whose premise lies in P together with what the earlier
  steps derived, until Q is derived.

The derivation is found by forward chaining that records, for every
attribute, the step that derived it (with counters on the premises, as in the
LinClosure algorithm of Beeri and Bernstein, so in time linear in the size of
L), and then by going backwards from Q to the steps it needs: the derivation
DAG of Maier, written out in the order of the steps. The steps it needs make
a subset of L that entails P -> Q but need not be minimal, since an attribute
may be derived once on a route the others do not need; it is made minimal by
deleting each implication in turn and keeping it out when P -> Q still
follows. That costs one closure per implication of the subset.

A minimal subset need not have the fewest implications: finding one of
minimum size is NP-hard (Baader, Peñaloza and Suntisrivaraporn, 2007), and
there can be exponentially many minimal subsets; which one is found depends
on the order of deletion, here the last steps first.
"""

from collections import deque
from collections.abc import Hashable, Iterable, Sequence, Set
from dataclasses import dataclass
from typing import Generic, TypeVar

from ..core.implication import Implication

A = TypeVar("A", bound=Hashable)


@dataclass(frozen=True)
class Step(Generic[A]):
    """The application of an implication: the attributes it derives that were
    not known before."""

    implication: Implication[A]
    derived: frozenset[A]


@dataclass(frozen=True)
class Explanation(Generic[A]):
    """Why P -> Q follows: the steps of a derivation from a minimal subset of
    the implications, which are the implications of the steps."""

    premise: frozenset[A]
    conclusion: frozenset[A]
    steps: tuple[Step[A], ...]

    @property
    def implications(self) -> tuple[Implication[A], ...]:
        return tuple(step.implication for step in self.steps)


def _forward(premise: Set[A], implications: Sequence[Implication[A]], goal: Set[A]):
    """Forward chaining from the premise until the goal is derived: the steps
    taken, by the position of their implication, and for each derived
    attribute the step that derived it."""
    known = set(premise)
    waiting = []  # per implication, how many premise attributes are not known
    watchers: dict[A, list[int]] = {}
    ready = deque()
    for position, implication in enumerate(implications):
        missing = implication.premise - known
        waiting.append(len(missing))
        for attribute in missing:
            watchers.setdefault(attribute, []).append(position)
        if not missing:
            ready.append(position)
    steps: list[int] = []
    reason: dict[A, int] = {}
    # First in, first out, so that what needs fewer steps is derived first.
    while ready and not goal <= known:
        position = ready.popleft()
        new = implications[position].conclusion - known
        if not new:
            continue
        for attribute in new:
            reason[attribute] = len(steps)
            for other in watchers.get(attribute, ()):
                waiting[other] -= 1
                if waiting[other] == 0:
                    ready.append(other)
        known |= new
        steps.append(position)
    return known, steps, reason


def _needed(premise: Set[A], goal: Set[A], steps: list[int], reason: dict[A, int],
            implications: Sequence[Implication[A]]) -> list[int]:
    """The steps the goal needs, going backwards from it, in their order."""
    needed: set[int] = set()
    pending = [a for a in goal if a not in premise]
    seen = set(pending)
    while pending:
        step = reason[pending.pop()]
        if step in needed:
            continue
        needed.add(step)
        for attribute in implications[steps[step]].premise:
            if attribute not in premise and attribute not in seen:
                seen.add(attribute)
                pending.append(attribute)
    return [steps[step] for step in sorted(needed)]


def derivation(premise: Iterable[A], conclusion: Iterable[A],
               implications: Iterable[Implication[A]]) -> Explanation[A] | None:
    """A derivation of premise -> conclusion from the implications, made of
    the steps that forward chaining needs for it; None if the implications do
    not entail it."""
    premise, conclusion = frozenset(premise), frozenset(conclusion)
    implications = list(implications)
    known, steps, reason = _forward(premise, implications, conclusion)
    if not conclusion <= known:
        return None
    applied = set(premise)
    result = []
    for position in _needed(premise, conclusion, steps, reason, implications):
        implication = implications[position]
        result.append(Step(implication, frozenset(implication.conclusion - applied)))
        applied |= implication.conclusion
    return Explanation(premise, conclusion, tuple(result))


def explain(premise: Iterable[A], conclusion: Iterable[A],
            implications: Iterable[Implication[A]]) -> Explanation[A] | None:
    """An explanation of premise -> conclusion by the implications: a
    derivation from a minimal subset of them that entails it; None if they do
    not entail it."""
    premise, conclusion = frozenset(premise), frozenset(conclusion)
    found = derivation(premise, conclusion, implications)
    if found is None:
        return None
    subset = list(found.implications)
    # Delete each implication in turn, the last steps first, and keep it out
    # when the rest still entail the implication.
    for implication in reversed(found.implications):
        rest = [i for i in subset if i != implication]
        if conclusion <= _forward(premise, rest, conclusion)[0]:
            subset = rest
    return derivation(premise, conclusion, subset)


def is_derivation(explanation: Explanation[A]) -> bool:
    """Whether each step applies an implication whose premise is known by
    then, derives what it claims, and the steps together derive the
    conclusion."""
    known = set(explanation.premise)
    for step in explanation.steps:
        if not step.implication.premise <= known:
            return False
        if step.derived != step.implication.conclusion - known:
            return False
        known |= step.implication.conclusion
    return explanation.conclusion <= known
