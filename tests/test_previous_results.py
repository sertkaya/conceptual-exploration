"""Unit tests for collecting the results of earlier explorations for new laws."""

import json
import random

import numpy as np
import pytest

from explorations.equational_theories import etp
from explorations.equational_theories.explore import load_free_magmas
from explorations.equational_theories.magma import Equation
from explorations.equational_theories.previous_results import holds, irreducible, main
from explorations.equational_theories.vampire import FreeMagma

# The first five laws of the ETP, and which implies which: everything implies
# x = x, x = y implies everything, and x = x * y and x = y * x imply x = x * x.
LAWS = ["x = x", "x = y", "x = x ◇ x", "x = x ◇ y", "x = y ◇ x"]
IMPLIES = {(a, b) for a in range(1, 6) for b in range(1, 6)
           if a == b or b == 1 or a == 2 or (a in (4, 5) and b == 3)}
LEFT_PROJECTION = [[0, 0], [1, 1]]  # x * y = x


def rle(outcomes):
    runs = []
    for value in outcomes:
        if runs and runs[-2] == value:
            runs[-1] += 1
        else:
            runs += [value, 1]
    return runs


@pytest.fixture
def data(tmp_path):
    equations = tmp_path / "equations.txt"
    equations.write_text("\n".join(LAWS) + "\n", encoding="utf-8")
    graph = tmp_path / "graph.json"
    outcomes = [7 if (a, b) in IMPLIES else 6 for a in range(1, 6) for b in range(1, 6)]
    graph.write_text(json.dumps({"rle_encoded_array": rle(outcomes)}))
    return equations, graph


def test_the_laws_can_be_limited_to_few_variables(data, tmp_path):
    output = tmp_path / "laws.json"
    etp.main([str(data[0]), "--max-order", "1", "--max-variables", "1", "--graph", str(data[1]), "-o", str(output)])
    assert [entry["id"] for entry in json.loads(output.read_text())] == [1, 3]


def test_laws_hold_in_a_table_as_they_do_one_assignment_at_a_time():
    random.seed(0)
    laws = [Equation.parse(s) for s in ["x = x * x", "x * y = y * x", "x = (y * x) * y", "x * (y * z) = (x * y) * z"]]
    for n in (1, 2, 3, 4):
        for _ in range(30):
            table = [[random.randrange(n) for _ in range(n)] for _ in range(n)]
            for law in laws:
                assert holds(law, np.array(table)) == law.holds_in_table(n, table)


def test_rows_that_are_intersections_of_larger_rows_are_dropped():
    assert irreducible([0b011, 0b101, 0b001, 0b111], 3) == [0, 1, 3]
    assert irreducible([0b001, 0b011], 2) == [0, 1]


def test_magmas_free_magmas_and_proofs_are_carried_over_to_the_new_laws(data, tmp_path):
    new = tmp_path / "new.json"
    etp.main([str(data[0]), "1", "2", "3", "4", "-o", str(new)])  # with the dual of law 4, law 5
    # An earlier exploration of the same laws with other variables and ids.
    old = tmp_path / "old.json"
    old.write_text(json.dumps([{"id": 10, "equation": "a = a * a"}, {"id": 11, "equation": "a = a * b"},
                               {"id": 12, "equation": "a = b * a"}, {"id": 13, "equation": "a = b"}]))
    results = tmp_path / "results"
    results.mkdir()
    (results / "magmas.json").write_text(json.dumps([{"name": "L", "size": 2, "table": LEFT_PROJECTION}]))
    (results / "free_magmas.json").write_text(json.dumps(
        [{"name": "F1", "dual_of": None, "premise": [10], "positive": [10], "negative": [11]}]))
    (results / "implications.json").write_text(json.dumps([
        {"premise": [11], "conclusion": [10], "source": "confirmed"},
        {"premise": [10], "conclusion": [12], "source": "unconfirmed"},
        # Earlier results label the dual of an unconfirmed implication mapped.
        {"premise": [10], "conclusion": [11], "source": "mapped"},
    ]))
    output = tmp_path / "out"
    main([str(new), "--etp-equations", str(data[0]), "--graph", str(data[1]),
          "--results", f"{results}={old}", "--proofs", f"{results}={old}", "-o", str(output)])
    # The left projection and its dual, the right projection.
    tables = sorted(etp.load_tables(output / "magmas.txt"), key=lambda m: m.table)
    assert [m.table for m in tables] == [((0, 0), (1, 1)), ((0, 1), (0, 1))]
    # The free magma satisfies x = x * x, hence x = x, and violates x = x * y, hence x = y.
    assert json.loads((output / "free_magmas.json").read_text()) == [
        {"premise": ["a = (a * a)"], "positive": [1, 3], "negative": [2, 4]}]
    # The confirmed implication and its dual, but neither the unconfirmed one nor its dual.
    background = json.loads((output / "background.json").read_text())
    assert sorted(map(json.dumps, background)) == sorted(map(json.dumps, [
        {"premise": [4], "conclusion": [3]}, {"premise": [5], "conclusion": [3]}]))


def test_the_proofs_of_a_vampire_log_are_carried_over(data, tmp_path):
    new = tmp_path / "new.json"
    etp.main([str(data[0]), "1", "2", "3", "4", "-o", str(new)])
    log = tmp_path / "run.log"
    log.write_text("\n".join([
        "Expert:                   Vampire, 10 s to prove",
        "Exploring 3 Equational Laws:",
        "  - Eq1: x = x",
        "  - Eq3: x = (x * x)",
        "  - Eq4: x = (x * y)",
        "Question 1: Eq1: x = x, Eq4: x = (x * y) -> Eq3: x = (x * x)",
        "Confirmed",
        "Question 2: Eq1: x = x, Eq3: x = (x * x) -> Eq4: x = (x * y)",
        "Counterexample found: Free magma over {Eq1, Eq3}",
        "Satisfies: Eq1: x = x, Eq3: x = (x * x)",
        "Does not satisfy: Eq4: x = (x * y)",
        "",
    ]))
    output = tmp_path / "out"
    main([str(new), "--etp-equations", str(data[0]), "--graph", str(data[1]), "--logs", str(log),
          "-o", str(output)])
    assert json.loads((output / "background.json").read_text()) == [
        {"premise": [1, 4], "conclusion": [3]}, {"premise": [1, 5], "conclusion": [3]}]
    assert json.loads((output / "free_magmas.json").read_text()) == [
        {"premise": ["x = (x * x)", "x = x"], "positive": [1, 3], "negative": [2, 4]}]


def test_free_magmas_are_read_as_objects_known_on_their_laws(tmp_path):
    equations = [Equation.parse(s, id=k) for k, s in [(1, "x = x"), (3, "x = x * x"), (4, "x = x * y")]]
    path = tmp_path / "free.json"
    path.write_text(json.dumps([{"premise": [3, "x = (y * x) * y"], "positive": [1, 3], "negative": [4]}]))
    (free,) = load_free_magmas(path, equations)
    assert isinstance(free.object, FreeMagma)
    assert free.positive == set(equations[:2]) and free.negative == {equations[2]}
    path.write_text(json.dumps([{"premise": [], "positive": [7], "negative": []}]))
    with pytest.raises(ValueError, match="not among the equations"):
        load_free_magmas(path, equations)
