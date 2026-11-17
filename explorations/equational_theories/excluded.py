"""Exploring the laws of magmas outside the varieties of some laws.

Most hard questions of an exploration can concern the magmas of a few laws,
such as Eq255: x = ((x * x) * x) * x and its dual Eq47 among the laws of order
at most three. With these laws E excluded, the exploration explores the
closure system C' of the closed sets of the theory of all magmas that contain
no law of E, together with the set of all laws: the theory of all magmas
together with the implications {e} -> all laws, for each e in E, given as
background. A set of laws whose closure contains no law of E has the same
closure in C' as in the theory of all magmas, and every other set has all
laws as its closure. So the exploration finds every implication whose
premise implies no law of E, and asks no question about the inside of the
varieties of E, which can be explored apart, each with its law as an axiom.

In C', an implication P -> q holds exactly when P implies q or a law of E in
all magmas: if P implies none of them, the free magma over P violates them
all at once, and refutes it; if P implies one, everything holds there. The
objects of C' are the magmas that violate every law of E. ExcludingExpert
answers its questions with any expert for all magmas:

1. A proof of P -> Q holds in C' as well.
2. A counterexample that violates every law of E is one in C' as well.
3. Any other counterexample shows the laws it violates not to follow from P.
   Each law e of E it does not violate is then asked about: if P implies e,
   P -> Q holds in C'; if a counterexample shows P not to imply e, the free
   magma over P violates e as well, and once every law of E is so violated,
   the free magma over P, known to violate all these laws, is the
   counterexample in C'. If the expert cannot decide P -> e, neither is
   P -> Q decided.
4. An answer that P -> Q is false without a counterexample holds in C' only
   if P implies no law of E, which is asked in the same way.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.experts.base import Expert, Undecided
from explorations.equational_theories.etp import EtpRefutation
from explorations.equational_theories.magma import Equation
from explorations.equational_theories.vampire import FreeMagma


def excluded_background(equations: Sequence[Equation], excluded: Iterable[Equation]) -> list[Implication[Equation]]:
    """The implications {e} -> all laws, for each excluded law e."""
    return [Implication([e], equations) for e in excluded]


class ExcludingExpert(Expert[object, Equation]):
    """Answers the questions of the closure system with the laws `excluded`
    excluded, using `expert`, which answers them for all magmas (see the
    module docstring). `last_status` and `answers` count the answers of the
    kinds the exclusion adds; the expert counts its own."""

    def __init__(self, expert: Expert, excluded: Iterable[Equation]) -> None:
        self.expert = expert
        self.excluded = frozenset(excluded)
        self.last_status: str | None = None
        self.answers: dict[str, int] = {}

    def _count(self, status: str | None) -> None:
        self.last_status = status
        if status is not None:
            self.answers[status] = self.answers.get(status, 0) + 1

    def _valid(self, obj: PartialObject) -> bool:
        return self.excluded <= set(obj.negative)

    def validate(
        self,
        implication: Implication[Equation],
        attributes: Iterable[Equation] | None = None,
    ) -> PartialObject | Undecided | None:
        answer = self.expert.validate(implication, attributes)
        if answer is None:
            self._count(None)
            return None
        premise = frozenset(implication.premise)
        if isinstance(answer, Undecided):
            # A partial row that satisfies an excluded law is no object of C'.
            obj = answer.object if answer.object is not None and self._valid(answer.object) else None
            if not answer.rejected:
                self._count(None)
                return Undecided(answer.proved, obj, False)
            # False as a whole for all magmas, so also in C' if P implies no
            # law of E.
            verdict = self._excluded_follow(premise, set(), attributes)
            if verdict is True:
                self._count("excluded law follows")
                return None
            self._count(None if verdict is not None else "excluded law undecided")
            return Undecided(answer.proved, obj, verdict is not None)
        if self._valid(answer):
            self._count(None)
            return answer
        # A counterexample for all magmas that satisfies a law of E, or is not
        # known to violate it: what it violates does not follow from P.
        negative = set(answer.negative)
        verdict = self._excluded_follow(premise, negative, attributes)
        if verdict is True:
            self._count("excluded law follows")
            return None
        if verdict is None:
            self._count("excluded law undecided")
            return Undecided(frozenset(), None, False)
        self._count("free magma outside")
        positive = set(premise)
        if isinstance(answer.object, FreeMagma):
            positive |= set(answer.positive)
        return PartialObject(FreeMagma(premise), positive, negative)

    def _excluded_follow(
        self,
        premise: frozenset[Equation],
        negative: set[Equation],
        attributes: Iterable[Equation] | None,
    ) -> bool | None:
        """Whether the premise implies a law of E: True if it implies one,
        False if it implies none, None if that is not decided. `negative`
        holds laws known not to follow from the premise; the laws found not to
        follow on the way are added to it."""
        for law in sorted(self.excluded - negative):
            if law in negative:
                continue  # violated by the counterexample of an earlier law
            answer = self.expert.validate(Implication(premise, [law]), attributes)
            if answer is None:
                return True
            if isinstance(answer, Undecided):
                return None
            negative |= set(answer.negative)
        return False

    def is_conclusive(self) -> bool:
        return self.expert.is_conclusive()

    def new_objects(self) -> list[PartialObject]:
        # Only the magmas that violate every law of E are objects of C'.
        return [o for o in self.expert.new_objects() if self._valid(o)]


def outside(objects: Sequence[PartialObject], excluded: Iterable[Equation]) -> list[PartialObject]:
    """The objects of C' among the objects for all magmas: those known to
    violate every law of E. A refutation of the ETP graph stands for the free
    magma over a single law, whose laws, the ones it implies, are all known:
    it violates the laws of E it does not satisfy, and is kept if it
    satisfies none."""
    excluded = frozenset(excluded)
    kept = []
    for o in objects:
        if isinstance(o.object, EtpRefutation) and not excluded & set(o.positive):
            kept.append(PartialObject(o.object, set(o.positive), set(o.negative) | excluded))
        elif excluded <= set(o.negative):
            kept.append(o)
    return kept
