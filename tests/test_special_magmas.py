"""Unit tests for counterexamples among linear and translation-invariant magmas."""

import json
import random

import pytest

from explorations.equational_theories.magma import Equation
from explorations.equational_theories.special_magmas import (
    LinearMagma,
    Ring,
    _translation_invariant_premise,
    cyclic,
    small_groups,
    find_translation_invariant,
    linear_magmas,
    main,
    translation_invariant_magma,
)

pytest.importorskip("pysat")

LAWS = [Equation.parse(s, id=k) for k, s in enumerate([
    "x = x * x",
    "x * y = y * x",
    "x = y * (y * (y * x))",
    "x = ((y * x) * x) * y",
    "x * (y * z) = (x * y) * z",
    "x = (x * y) * (y * x)",
    "x * x = y * y",
    "x = y",
], start=1)]
IDEMPOTENT, COMMUTATIVE, EQ75, EQ271, ASSOCIATIVE, _, _, TRIVIAL = LAWS


def test_a_linear_magma_satisfies_the_laws_its_table_satisfies():
    random.seed(0)
    magmas = list(linear_magmas(8, [(2, 2), (3, 2), (2, 4)]))
    for linear in random.sample(magmas, 200):
        magma = linear.magma()
        assert [linear.satisfies(law) for law in LAWS] == [law.holds_in_magma(magma) for law in LAWS]


@pytest.mark.parametrize("dim, modulus", [(2, 2), (2, 3), (2, 4)])
def test_matrices_up_to_conjugacy_give_every_row_of_all_matrices(dim, modulus):
    ring = Ring(modulus, dim)
    every = {LinearMagma(ring, a, b, ring.zero).satisfied(LAWS) for a in ring.elements() for b in ring.elements()}
    reduced = {linear.satisfied(LAWS) for linear in linear_magmas(2, [(dim, modulus)])}
    assert reduced == every


def test_a_linear_magma_of_size_19_refutes_that_three_laws_force_the_trivial_magma():
    magma = LinearMagma(Ring(19), 13, 7).magma()
    assert all(law.holds_in_magma(magma) for law in (IDEMPOTENT, EQ75, EQ271))
    assert not TRIVIAL.holds_in_magma(magma)


@pytest.mark.parametrize("group", [cyclic(3), cyclic(5)] + [g for g in small_groups(8) if g.order <= 8],
                         ids=lambda g: g.name)
def test_the_premise_encoding_agrees_with_the_tables(group):
    random.seed(1)
    n = group.order
    solvers = [_translation_invariant_premise([law], group) for law in LAWS]
    for _ in range(15):
        f = [random.randrange(n) for _ in range(n)]
        magma = translation_invariant_magma(f, group)
        for law, (solver, F) in zip(LAWS, solvers):
            holds = solver is not None and solver.solve(assumptions=[F[d][f[d]] for d in range(n)])
            assert holds == law.holds_in_magma(magma)


def test_the_small_groups_are_groups_of_the_stated_orders():
    groups = {g.name: g for g in small_groups(24)}
    orders = {"Z/2 x Z/2": 4, "(Z/2)^3": 8, "D3": 6, "Q8": 8, "Dic3": 12, "A4": 12, "S4": 24, "Z/2 x Z/12": 24}
    assert {name: groups[name].order for name in orders} == orders
    for g in groups.values():
        elements = range(g.order)
        assert all(g.mul(0, a) == a == g.mul(a, 0) for a in elements)
        assert all(g.mul(g.mul(a, b), c) == g.mul(a, g.mul(b, c)) for a in elements for b in elements for c in elements)
    abelian = lambda g: all(g.mul(a, b) == g.mul(b, a) for a in range(g.order) for b in range(g.order))
    assert not abelian(groups["Q8"]) and not abelian(groups["D3"]) and abelian(groups["Z/2 x Z/2"])


def test_the_smallest_translation_invariant_counterexample_has_19_elements():
    premise = [IDEMPOTENT, EQ75, EQ271]
    assert all(find_translation_invariant(premise, [TRIVIAL], n) is None for n in range(2, 19))
    magma = find_translation_invariant(premise, [TRIVIAL], 19)
    assert magma is not None and magma.size == 19
    assert all(law.holds_in_magma(magma) for law in premise) and not TRIVIAL.holds_in_magma(magma)


def test_main_reports_the_refuted_questions_and_writes_their_tables(tmp_path, capsys):
    equations = tmp_path / "equations.json"
    equations.write_text(json.dumps([{"id": law.id, "equation": f"{law.lhs} = {law.rhs}"} for law in LAWS]))
    results = tmp_path / "results"
    results.mkdir()
    (results / "implications.json").write_text(json.dumps([
        {"premise": [1, 3, 4], "conclusion": [8], "source": "unconfirmed"},
        {"premise": [5], "conclusion": [5], "source": "confirmed"},
        {"premise": [1, 2, 5], "conclusion": [7], "source": "open"},
    ]))
    tables = tmp_path / "tables.txt"
    main([str(results), "--equations", str(equations), "--max-modulus", "20",
          "--matrices", "--translation-invariant-size", "4", "-o", str(tables)])
    out = capsys.readouterr().out
    assert "unconfirmed Eq1, Eq3, Eq4 -> ... refuted by x*y = " in out and "mod 19" in out
    # Idempotent commutative semigroups (semilattices) with x * x = y * y are trivial,
    # so the open question is not refuted.
    assert "open " not in out.split("questions refuted")[-1]
    assert len(tables.read_text().splitlines()) == 1
