"""Unit tests for explaining implications from an exploration's results."""

import json

import pytest

from explorations.equational_theories.explain import main


@pytest.fixture
def results(tmp_path):
    equations = tmp_path / "laws.json"
    equations.write_text(json.dumps([{"id": n, "equation": e} for n, e in
                                     [(1, "x = x"), (3, "x = x * x"), (4, "x = x * y"), (5, "x = y * x"), (2, "x = y")]]))
    directory = tmp_path / "results"
    directory.mkdir()
    (directory / "implications.json").write_text(json.dumps([
        {"premise": [], "conclusion": [1], "source": "background"},
        {"premise": [4], "conclusion": [3], "source": "confirmed"},
        {"premise": [3, 5], "conclusion": [2], "source": "unconfirmed"},
        {"premise": [4, 5], "conclusion": [2], "source": "confirmed"},
    ]))
    return directory, equations


def test_a_derivation_is_printed_step_by_step_with_sources(results, capsys):
    directory, equations = results
    main([str(directory), "--equations", str(equations), "--premise", "4", "--conclusion", "3", "1"])
    out = capsys.readouterr().out
    assert "minimal set of 2 of them" in out
    assert "(nothing) -> Eq1   [background]" in out and "Eq4 -> Eq3   [confirmed]" in out
    assert "So Eq4 -> Eq1, Eq3." in out


def test_unconfirmed_implications_are_used_only_when_asked_and_marked(results, capsys):
    directory, equations = results
    main([str(directory), "--equations", str(equations), "--premise", "4", "5", "--conclusion", "2"])
    assert "[unconfirmed]" not in capsys.readouterr().out
    with pytest.raises(SystemExit):
        main([str(directory), "--equations", str(equations), "--premise", "3", "5", "--conclusion", "2"])
    assert "It does not follow from them." in capsys.readouterr().out
    main([str(directory), "--equations", str(equations), "--premise", "3", "5", "--conclusion", "2",
          "--unconfirmed"])
    assert "Eq3, Eq5 -> Eq2   [unconfirmed]  (not proved)" in capsys.readouterr().out
