"""Put the unproved laws of an exploration's unconfirmed implications and open
questions to the E theorem prover (https://eprover.org).

Each law of the conclusion of an unconfirmed implication or open question is
posed on its own, with the premise as axioms, and a law and its dual under the
same dual premise are posed once. E either proves the law (Theorem), shows it
not derivable by saturation (CounterSatisfiable), so that the free magma over
the premise refutes it, or gives up within the time limit.

    python -m explorations.equational_theories.eprover_batch \
        results/order3_vampire_mace4_etp_refutations_duals_asked --time-limit 60
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tempfile
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from explorations.equational_theories.magma import Equation
from explorations.equational_theories.vampire import tptp_problem

HERE = Path(__file__).resolve().parent


def load_laws(path: Path) -> dict[int, Equation]:
    entries = json.loads(path.read_text(encoding="utf-8"))
    return {entry["id"]: Equation.parse(entry["equation"], id=entry["id"]) for entry in entries}


def dual_numbers(laws: dict[int, Equation]) -> dict[int, int]:
    """The number of the dual of each law, among the laws given."""
    duals = {}
    for number, law in laws.items():
        dual = law.dual()
        matches = [other for other, candidate in laws.items() if dual.is_equivalent_to(candidate)]
        if len(matches) != 1:
            raise ValueError(f"The dual of Eq{number} matches {matches}")
        duals[number] = matches[0]
    return duals


def run_eprover(problem: str, time_limit: int) -> tuple[str, float]:
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as file:
        file.write(problem)
        path = Path(file.name)
    start = time.monotonic()
    try:
        run = subprocess.run(
            ["eprover", "--auto-schedule", f"--cpu-limit={time_limit}", "-s", str(path)],
            capture_output=True,
            text=True,
        )
    finally:
        path.unlink(missing_ok=True)
    status = re.search(r"SZS status (\w+)", run.stdout)
    return (status.group(1) if status else "Unknown"), time.monotonic() - start


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("results", type=Path, help="directory with the exploration's implications.json")
    parser.add_argument("--equations", type=Path, default=HERE / "equations_order3.json")
    parser.add_argument("--time-limit", type=int, default=60, help="CPU seconds per law (default 60)")
    parser.add_argument("--jobs", type=int, default=8, help="parallel E processes (default 8)")
    parser.add_argument("--output", type=Path, help="JSON file for the results (default: eprover.json in RESULTS)")
    args = parser.parse_args()
    if shutil.which("eprover") is None:
        parser.error("eprover is not on the PATH")

    laws = load_laws(args.equations)
    dual = dual_numbers(laws)
    implications = json.loads((args.results / "implications.json").read_text(encoding="utf-8"))

    # One question per law of a conclusion, up to duality.
    questions: dict[tuple[tuple[int, ...], int], list[dict]] = {}
    for implication in implications:
        if implication["source"] not in ("unconfirmed", "open"):
            continue
        premise = tuple(sorted(implication["premise"]))
        for law in implication["conclusion"]:
            key = (premise, law)
            dual_key = (tuple(sorted(dual[n] for n in premise)), dual[law])
            key = min(key, dual_key)
            questions.setdefault(key, []).append(implication)
    print(f"{len(questions)} laws to decide, up to duality", flush=True)

    def decide(key: tuple[tuple[int, ...], int]) -> dict:
        premise, law = key
        problem = tptp_problem([laws[n] for n in premise], [laws[law]])
        status, seconds = run_eprover(problem, args.time_limit)
        return {"premise": list(premise), "law": law, "status": status, "seconds": round(seconds, 2)}

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for k, result in enumerate(pool.map(decide, questions), 1):
            results.append(result)
            if result["status"] in ("Theorem", "CounterSatisfiable"):
                print(f"[{k}/{len(questions)}] {result['status']}: Eq{result['law']} from "
                      f"{', '.join(f'Eq{n}' for n in result['premise'])} ({result['seconds']} s)", flush=True)
            elif k % 50 == 0:
                print(f"[{k}/{len(questions)}] ...", flush=True)

    output = args.output or args.results / "eprover.json"
    output.write_text(json.dumps(results, indent=1) + "\n", encoding="utf-8")
    print(Counter(result["status"] for result in results))
    print(f"Results written to {output}")


if __name__ == "__main__":
    main()
