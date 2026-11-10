"""Unit tests for explanations of entailments between implications."""

import random

from conceptual_exploration.algorithms.explanation import derivation, explain, is_derivation
from conceptual_exploration.core.implication import Implication
from conceptual_exploration.core.theory import ImplicationTheory


def imp(premise: str, conclusion: str) -> Implication[str]:
    return Implication(premise, conclusion)


def test_a_chain_is_derived_step_by_step():
    found = explain("a", "d", [imp("c", "d"), imp("a", "b"), imp("b", "c")])
    assert [(str(s.implication), set(s.derived)) for s in found.steps] == [
        ("a -> b", {"b"}), ("b -> c", {"c"}), ("c -> d", {"d"})]


def test_only_the_implications_the_conclusion_needs_are_kept():
    found = explain("a", "c", [imp("a", "b"), imp("a", "c"), imp("b", "e")])
    assert found.implications == (imp("a", "c"),)


def test_a_premise_of_several_attributes_waits_for_all_of_them():
    found = explain("ab", "e", [imp("cd", "e"), imp("a", "c"), imp("b", "d")])
    assert set(found.implications) == {imp("cd", "e"), imp("a", "c"), imp("b", "d")}
    assert found.implications[-1] == imp("cd", "e") and is_derivation(found)


def test_what_is_in_the_premise_needs_no_step():
    assert explain("ab", "a", [imp("a", "b")]).steps == ()


def test_what_does_not_follow_has_no_explanation():
    assert explain("a", "c", [imp("a", "b"), imp("bd", "c")]) is None
    assert derivation("a", "c", [imp("a", "b"), imp("bd", "c")]) is None


def test_the_deletion_drops_a_route_the_others_make_unnecessary():
    # Forward chaining derives d by a -> b and b -> d before e -> c, d fires,
    # so the derivation of c, d needs four implications; two of them suffice.
    implications = [imp("a", "b"), imp("a", "e"), imp("b", "d"), imp("e", "cd")]
    assert len(derivation("a", "cd", implications).steps) == 4
    found = explain("a", "cd", implications)
    assert found.implications == (imp("a", "e"), imp("e", "cd")) and is_derivation(found)


def test_random_explanations_are_minimal_derivations():
    random.seed(0)
    attributes = "abcdefgh"
    for _ in range(300):
        implications = [
            imp("".join(random.sample(attributes, random.randint(0, 2))),
                "".join(random.sample(attributes, random.randint(1, 2))))
            for _ in range(random.randint(1, 12))
        ]
        premise = random.sample(attributes, random.randint(0, 2))
        conclusion = random.sample(attributes, random.randint(1, 3))
        theory = ImplicationTheory(implications)
        found = explain(premise, conclusion, implications)
        assert (found is not None) == theory.entails(Implication(premise, conclusion))
        if found is None:
            continue
        assert is_derivation(found)
        assert set(found.implications) <= set(implications)
        assert len(set(found.implications)) == len(found.implications)
        for dropped in found.implications:
            rest = [i for i in found.implications if i != dropped]
            assert not ImplicationTheory(rest).entails(Implication(premise, conclusion))
