"""Unit tests for exploring the laws of magmas outside the varieties of some laws."""

import itertools
import json
import shutil

import pytest

from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.core.theory import ImplicationTheory
from conceptual_exploration.experts.base import Expert, Undecided
from explorations.equational_theories.etp import EtpRefutation
from explorations.equational_theories.excluded import ExcludingExpert, excluded_background, outside
from explorations.equational_theories.explore import run_magma_exploration
from explorations.equational_theories.magma import Equation, Magma
from explorations.equational_theories.vampire import FreeMagma

E1, E2, P, Q, R = (Equation.parse(s) for s in
                   ["x = (x * x) * x", "x = x * (x * x)", "x * y = y * x", "x = x * y", "x = y"])
EXCLUDED = {E1, E2}


class Scripted(Expert):
    """Answers each question by its conclusion, and records the questions."""

    def __init__(self, answers):
        self.answers, self.asked, self.extra = answers, [], []

    def validate(self, implication, attributes=None):
        self.asked.append(implication)
        return self.answers[frozenset(implication.conclusion)]

    def new_objects(self):
        return self.extra


def obj(positive, negative, name="M"):
    return PartialObject(Magma(1, ((0,),), name) if name else name, set(positive), set(negative))


def test_proofs_and_counterexamples_outside_the_varieties_are_passed_on():
    question = Implication([P], [Q])
    assert ExcludingExpert(Scripted({frozenset([Q]): None}), EXCLUDED).validate(question) is None
    good = obj([P], [Q, E1, E2])
    assert ExcludingExpert(Scripted({frozenset([Q]): good}), EXCLUDED).validate(question) is good


def test_a_counterexample_inside_a_variety_is_replaced_by_the_free_magma():
    # It satisfies E1; the premise is then found to imply neither E1 nor E2.
    inner = Scripted({frozenset([Q]): obj([P, E1], [Q, E2]), frozenset([E1]): obj([P], [E1, R])})
    answer = ExcludingExpert(inner, EXCLUDED).validate(Implication([P], [Q]))
    assert inner.asked[1:] == [Implication([P], [E1])]
    assert isinstance(answer.object, FreeMagma) and answer.object.premise == {P}
    assert answer.positive == {P} and answer.negative == {Q, E1, E2, R}


def test_the_question_holds_when_the_premise_implies_an_excluded_law():
    inner = Scripted({frozenset([Q]): obj([P, E1, E2], [Q]), frozenset([E1]): None})
    expert = ExcludingExpert(inner, EXCLUDED)
    assert expert.validate(Implication([P], [Q])) is None
    assert expert.last_status == "excluded law follows"


def test_the_question_is_undecided_when_an_excluded_law_is():
    inner = Scripted({frozenset([Q]): obj([P, E1], [Q, E2]), frozenset([E1]): Undecided()})
    answer = ExcludingExpert(inner, EXCLUDED).validate(Implication([P], [Q]))
    assert answer == Undecided(frozenset(), None, False)


def test_a_rejection_stands_only_if_no_excluded_law_follows():
    rejected = Undecided(frozenset(), None, True)
    inner = Scripted({frozenset([Q]): rejected, frozenset([E1]): obj([P], [E1, E2])})
    assert ExcludingExpert(inner, EXCLUDED).validate(Implication([P], [Q])).rejected
    inner = Scripted({frozenset([Q]): rejected, frozenset([E1]): None})
    assert ExcludingExpert(inner, EXCLUDED).validate(Implication([P], [Q])) is None


def test_only_objects_violating_every_excluded_law_are_kept():
    inner = Scripted({})
    inner.extra = [obj([P], [E1, E2], "A"), obj([P, E1], [E2], "B"), obj([P], [E2], "C")]
    assert [o.object.name for o in ExcludingExpert(inner, EXCLUDED).new_objects()] == ["A"]
    refutation = PartialObject(EtpRefutation(4, 3), {P}, {Q})
    inside = PartialObject(EtpRefutation(5, 3), {P, E1}, {Q})
    kept = outside([obj([P], [E1, E2], "A"), obj([P], [E2], "C"), refutation, inside], EXCLUDED)
    assert [o.object for o in kept] == [kept[0].object, EtpRefutation(4, 3)]
    assert kept[1].negative == {Q, E1, E2}


def test_the_background_lets_each_excluded_law_imply_every_law():
    laws = [P, Q, E1, E2]
    assert set(excluded_background(laws, [E1])) == {Implication([E1], laws)}


LAWS = ["x = x", "x = y", "x = x * x", "x = x * (x * x)", "x = (x * x) * x", "x * y = y * x",
        "x = x * y", "x = y * x"]


def closed_sets(theory, attributes):
    return {frozenset(s) for k in range(len(attributes) + 1) for s in itertools.combinations(attributes, k)
            if theory.closure(set(s)) == set(s)}


@pytest.mark.skipif(shutil.which("vampire") is None, reason="Vampire not installed")
def test_the_exploration_finds_the_closed_sets_outside_the_excluded_varieties(tmp_path):
    path = tmp_path / "laws.json"
    path.write_text(json.dumps([{"id": k, "equation": e} for k, e in enumerate(LAWS, start=1)]))
    _, full = run_magma_exploration(equations_path=path, expert_kind="vampire", report_interval=1000)
    _, part = run_magma_exploration(equations_path=path, expert_kind="vampire", report_interval=1000,
                                    excluded=[4, 5])
    attributes = list(full.attributes)
    excluded = {eq for eq in attributes if eq.id in (4, 5)}
    expected = {s for s in closed_sets(full.implications, attributes) if not s & excluded}
    expected.add(frozenset(attributes))
    assert closed_sets(part.implications, attributes) == expected


def test_an_axiom_without_its_dual_needs_the_duality_off(tmp_path):
    path = tmp_path / "laws.json"
    path.write_text(json.dumps([{"id": k, "equation": e} for k, e in enumerate(LAWS, start=1)]))
    with pytest.raises(ValueError, match="no-duality"):
        run_magma_exploration(equations_path=path, axioms=[5], report_interval=1000)


@pytest.mark.skipif(shutil.which("vampire") is None, reason="Vampire not installed")
def test_the_variety_of_an_axiom_has_the_closed_sets_that_contain_it(tmp_path):
    # Part B of an exclusion: with Eq5 as an axiom, the closed sets are those
    # of all magmas that contain it.
    path = tmp_path / "laws.json"
    path.write_text(json.dumps([{"id": k, "equation": e} for k, e in enumerate(LAWS, start=1)]))
    _, full = run_magma_exploration(equations_path=path, expert_kind="vampire", report_interval=1000)
    _, inside = run_magma_exploration(equations_path=path, expert_kind="vampire", report_interval=1000,
                                      axioms=[5], use_duality_symmetry=False)
    attributes = list(full.attributes)
    axiom = next(eq for eq in attributes if eq.id == 5)
    expected = {s for s in closed_sets(full.implications, attributes) if axiom in s}
    assert closed_sets(inside.implications, attributes) == expected
