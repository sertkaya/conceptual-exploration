"""Counterexamples among linear and translation-invariant magmas.

The model finders of the experts search all magmas of a size, which limits
them to sizes of about a dozen. Some classes of magmas are much easier to
search, and the ETP found many of its counterexamples in them:

- linear magmas, x * y = a x + b y + c, with a, b, c in Z/n, or a, b k x k
  matrices over Z/m acting on (Z/m)^k. Every term is then a linear form in its
  variables, and a law holds exactly when its two sides have the same
  coefficients, so each magma is evaluated on every law without its table;
- translation-invariant magmas, x * y = x + f(y - x) on Z/n, of which the
  idempotent linear magmas over Z/n are a special case, and more generally
  x * y = x f(x^-1 y) on a finite group. Left multiplications are
  automorphisms, so a law holds when it holds with its first variable the
  identity, and a SAT solver finds the functions f under which the premise of
  a question holds, n values instead of a table of n^2.

Every magma found is checked on its table before it is reported.

usage: special_magmas.py RESULTS_DIR --equations FILE [-o TABLES]

tries to refute the unconfirmed implications and open questions in
RESULTS_DIR/implications.json, and writes the magmas that refute them to
TABLES, one "Table [[...]]" per line, to be read with --seed-magmas or
--context-magmas.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections.abc import Iterable, Iterator, Sequence
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    # Run as a script: make the repository importable.
    _ROOT = Path(__file__).resolve().parent.parent.parent
    sys.path[:0] = [str(_ROOT / "src"), str(_ROOT)]

from explorations.equational_theories.magma import ETP, Equation, Magma, Term, Var


# Linear magmas. A ring element is an int mod m, or a k x k matrix over Z/m
# as a tuple of its k^2 entries, row by row.

@dataclass(frozen=True)
class Ring:
    modulus: int
    dim: int = 1

    @property
    def zero(self):
        return (0,) * (self.dim * self.dim) if self.dim > 1 else 0

    @property
    def one(self):
        k = self.dim
        return tuple(int(i == j) for i in range(k) for j in range(k)) if k > 1 else 1

    def add(self, u, v):
        if self.dim > 1:
            return tuple((s + t) % self.modulus for s, t in zip(u, v))
        return (u + v) % self.modulus

    def mul(self, u, v):
        k, m = self.dim, self.modulus
        if k > 1:
            return tuple(sum(u[i * k + l] * v[l * k + j] for l in range(k)) % m for i in range(k) for j in range(k))
        return (u * v) % m

    def elements(self) -> list:
        if self.dim > 1:
            return list(itertools.product(range(self.modulus), repeat=self.dim * self.dim))
        return list(range(self.modulus))

    def conjugacy_representatives(self) -> list:
        """One element of each class of elements conjugate by an invertible one."""
        elements = self.elements()
        units = [s for s in elements if any(self.mul(s, t) == self.one for t in elements)]
        inverse = {s: next(t for t in elements if self.mul(s, t) == self.one) for s in units}
        seen, representatives = set(), []
        for a in elements:
            if a in seen:
                continue
            representatives.append(a)
            seen.update(self.mul(self.mul(s, a), inverse[s]) for s in units)
        return representatives


@dataclass(frozen=True)
class LinearMagma:
    """x * y = a x + b y + c over a ring; c is 0 for matrices."""

    ring: Ring
    a: object
    b: object
    c: object = 0

    def __str__(self) -> str:
        r = self.ring
        if r.dim > 1:
            k = r.dim
            show = lambda m: [list(m[i * k:(i + 1) * k]) for i in range(k)]
            return f"x*y = Ax + By on (Z/{r.modulus})^{k}, A = {show(self.a)}, B = {show(self.b)}"
        constant = f" + {self.c}" if self.c else ""
        return f"x*y = {self.a}x + {self.b}y{constant} mod {r.modulus}"

    def _form(self, term: Term, cache: dict) -> tuple[dict[str, object], object]:
        """The coefficients of the variables of the term and its constant."""
        if term in cache:
            return cache[term]
        r = self.ring
        if isinstance(term, Var):
            form = {term.name: r.one}, r.zero
        else:
            (left, lc), (right, rc) = self._form(term.left, cache), self._form(term.right, cache)
            coefficients = {v: r.mul(self.a, k) for v, k in left.items()}
            for v, k in right.items():
                coefficients[v] = r.add(coefficients.get(v, r.zero), r.mul(self.b, k))
            constant = r.add(r.add(r.mul(self.a, lc), r.mul(self.b, rc)), self.c) if self.c else r.zero
            form = coefficients, constant
        cache[term] = form
        return form

    def satisfies(self, equation: Equation, cache: dict | None = None) -> bool:
        cache = {} if cache is None else cache
        (left, lc), (right, rc) = self._form(equation.lhs, cache), self._form(equation.rhs, cache)
        zero = self.ring.zero
        return lc == rc and all(left.get(v, zero) == right.get(v, zero) for v in set(left) | set(right))

    def satisfied(self, equations: Iterable[Equation]) -> frozenset[Equation]:
        cache: dict = {}
        return frozenset(eq for eq in equations if self.satisfies(eq, cache))

    def magma(self) -> Magma:
        r = self.ring
        m, k = r.modulus, r.dim
        if k == 1:
            return Magma(m, tuple(tuple((self.a * x + self.b * y + self.c) % m for y in range(m))
                                  for x in range(m)), name=str(self))
        vectors = list(itertools.product(range(m), repeat=k))
        index = {v: i for i, v in enumerate(vectors)}
        apply = lambda a, v: tuple(sum(a[i * k + j] * v[j] for j in range(k)) for i in range(k))
        return Magma(len(vectors), tuple(
            tuple(index[tuple((s + t) % m for s, t in zip(apply(self.a, x), apply(self.b, y)))] for y in vectors)
            for x in vectors), name=str(self))


def linear_magmas(max_modulus: int, matrix_rings: Iterable[tuple[int, int]] = ()) -> Iterator[LinearMagma]:
    """x * y = a x + b y + c over Z/n for n < max_modulus and c in {0, 1}, then
    x * y = A x + B y over (Z/m)^k for each (k, m), with A up to conjugacy: a
    conjugate pair of A and B gives an isomorphic magma."""
    for n in range(2, max_modulus):
        ring = Ring(n)
        for a, b in itertools.product(range(n), repeat=2):
            for c in (0, 1):
                yield LinearMagma(ring, a, b, c)
    for k, m in matrix_rings:
        ring = Ring(m, k)
        elements = ring.elements()
        for a in ring.conjugacy_representatives():
            for b in elements:
                yield LinearMagma(ring, a, b, ring.zero)


# Translation-invariant magmas, over a finite group G: x * y = x f(x^-1 y).

@dataclass(frozen=True)
class Group:
    """A finite group by its table, element 0 being the identity."""

    name: str
    table: tuple[tuple[int, ...], ...]

    @property
    def order(self) -> int:
        return len(self.table)

    def mul(self, a: int, b: int) -> int:
        return self.table[a][b]

    def inv(self, a: int) -> int:
        return self.table[a].index(0)

    @staticmethod
    def of(name: str, identity, elements: Iterable, mul) -> Group:
        elements = [identity] + [e for e in elements if e != identity]
        index = {e: i for i, e in enumerate(elements)}
        return Group(name, tuple(tuple(index[mul(a, b)] for b in elements) for a in elements))


def cyclic(n: int) -> Group:
    return Group(f"Z/{n}", tuple(tuple((a + b) % n for b in range(n)) for a in range(n)))


def _permutations(name: str, generators: Sequence[tuple[int, ...]]) -> Group:
    identity = tuple(range(len(generators[0])))
    compose = lambda p, q: tuple(p[i] for i in q)
    elements, frontier = {identity}, [identity]
    while frontier:
        frontier = [compose(g, e) for e in frontier for g in generators if compose(g, e) not in elements]
        elements.update(frontier)
    return Group.of(name, identity, sorted(elements), compose)


def small_groups(max_order: int) -> list[Group]:
    """Non-cyclic groups of order at most max_order: products of two cyclic
    groups, (Z/2)^3, the dihedral and dicyclic groups, A4 and S4."""
    groups = []
    for a in range(2, max_order + 1):
        for b in range(a, max_order // a + 1):
            if b % a == 0:
                groups.append(Group.of(f"Z/{a} x Z/{b}", (0, 0), itertools.product(range(a), range(b)),
                                       lambda u, v: ((u[0] + v[0]) % a, (u[1] + v[1]) % b)))
    if max_order >= 8:
        groups.append(Group.of("(Z/2)^3", (0, 0, 0), itertools.product(range(2), repeat=3),
                               lambda u, v: tuple((s + t) % 2 for s, t in zip(u, v))))
    for n in range(3, max_order // 2 + 1):
        groups.append(_permutations(f"D{n}", [tuple((i + 1) % n for i in range(n)), tuple((-i) % n for i in range(n))]))
    for n in range(2, max_order // 4 + 1):
        # Dic_n: a^k and a^k x, with a of order 2n, x^2 = a^n and x a = a^-1 x.
        def dic(u, v, n=n):
            (k, s), (m, t) = u, v
            return ((k + (-m if s else m) + (n if s and t else 0)) % (2 * n), s ^ t)
        groups.append(Group.of("Q8" if n == 2 else f"Dic{n}", (0, 0), itertools.product(range(2 * n), range(2)), dic))
    if max_order >= 12:
        groups.append(_permutations("A4", [(1, 2, 0, 3), (1, 0, 3, 2)]))
    if max_order >= 24:
        groups.append(_permutations("S4", [(1, 2, 3, 0), (1, 0, 2, 3)]))
    return sorted(groups, key=lambda g: g.order)


def _translation_invariant_premise(premise: Sequence[Equation], group: Group):
    """A SAT solver whose models are the functions f such that the magma
    x * y = x f(x^-1 y) on the group satisfies the premise, with the variable
    F[d][w] meaning f(d) = w; None if no f can satisfy it."""
    from pysat.solvers import Cadical153

    n, mul, inv = group.order, group.mul, group.inv
    F = [[1 + d * n + w for w in range(n)] for d in range(n)]
    top = n * n
    clauses: list[list[int]] = []

    def exactly_one(literals: list[int], at_least: bool) -> None:
        if at_least:
            clauses.append(literals)
        clauses.extend([[-u, -w] for u, w in itertools.combinations(literals, 2)])

    for row in F:
        exactly_one(row, True)
    # A value is an element, or a list of n variables, exactly one true.
    cache: dict[tuple, int | list[int]] = {}

    def fresh() -> list[int]:
        nonlocal top
        out = list(range(top + 1, top + n + 1))
        top += n
        exactly_one(out, False)  # at least one is implied by the clauses that define it
        return out

    def combine(a: int | list[int], b: int | list[int], g) -> list[int]:
        """The value g(a, b) for a function g on the group, by n^2 clauses at most."""
        out = fresh()
        lefts = [(a, [])] if isinstance(a, int) else [(i, [-a[i]]) for i in range(n)]
        rights = [(b, [])] if isinstance(b, int) else [(j, [-b[j]]) for j in range(n)]
        for (i, li), (j, lj) in itertools.product(lefts, rights):
            clauses.append(li + lj + [out[g(i, j)]])
        return out

    def apply_f(d: int | list[int]) -> list[int]:
        if isinstance(d, int):
            return F[d]
        out = fresh()
        clauses.extend([-d[i], -F[i][w], out[w]] for i in range(n) for w in range(n))
        return out

    def value(term: Term, env: dict[str, int]) -> int | list[int]:
        if isinstance(term, Var):
            return env[term.name]
        key = (term, tuple(sorted((v, env[v]) for v in term.vars())))
        if key in cache:
            return cache[key]
        a, b = value(term.left, env), value(term.right, env)
        if isinstance(a, int) and isinstance(b, int):
            out = [F[mul(inv(a), b)][mul(inv(a), v)] for v in range(n)]
        else:
            # a f(a^-1 b) in three steps of n^2 clauses each, not n^3 at once.
            out = combine(a, apply_f(combine(a, b, lambda i, j: mul(inv(i), j))), mul)
        cache[key] = out
        return out

    for equation in premise:
        variables = equation.variables
        for values in itertools.product(range(n), repeat=max(len(variables) - 1, 0)):
            env = dict(zip(variables, (0, *values)))
            left, right = value(equation.lhs, env), value(equation.rhs, env)
            if isinstance(left, int) and isinstance(right, int):
                if left != right:
                    return None, F
            elif isinstance(left, int):
                clauses.append([right[left]])
            elif isinstance(right, int):
                clauses.append([left[right]])
            else:
                for v in range(n):
                    clauses += [[-left[v], right[v]], [-right[v], left[v]]]
    return Cadical153(bootstrap_with=clauses), F


def translation_invariant_magma(f: Sequence[int], group: Group | None = None) -> Magma:
    group = group or cyclic(len(f))
    n, mul, inv = group.order, group.mul, group.inv
    if group.name.startswith("Z/") and " x " not in group.name:
        name = f"x*y = x + f(y - x) mod {n}, f = {list(f)}"
    else:
        name = f"x*y = x f(x^-1 y) on {group.name}, f = {list(f)}"
    return Magma(n, tuple(tuple(mul(x, f[mul(inv(x), y)]) for y in range(n)) for x in range(n)), name=name)


def _holds_at_identity(equation: Equation, magma: Magma) -> bool:
    """Whether a translation-invariant magma satisfies the law, which it does
    when it does with the first variable the identity 0."""
    variables = equation.variables
    for values in itertools.product(range(magma.size), repeat=max(len(variables) - 1, 0)):
        env = dict(zip(variables, (0, *values)))
        if equation.lhs.eval(env, magma.table) != equation.rhs.eval(env, magma.table):
            return False
    return True


def find_translation_invariant(
    premise: Sequence[Equation], conclusion: Sequence[Equation], group: Group | int, max_models: int = 200
) -> Magma | None:
    """A translation-invariant magma on the group (Z/n for an int n) that
    satisfies the premise and violates a law of the conclusion. The solver
    enumerates the models of the premise, excluding each that satisfies the
    conclusion, up to max_models; None if none is found."""
    group = cyclic(group) if isinstance(group, int) else group
    solver, F = _translation_invariant_premise(premise, group)
    if solver is None:
        return None
    n = group.order
    with solver:
        for _ in range(max_models):
            if not solver.solve():
                return None
            model = {literal for literal in solver.get_model() if literal > 0}
            f = [next(w for w in range(n) if F[d][w] in model) for d in range(n)]
            magma = translation_invariant_magma(f, group)
            if not all(_holds_at_identity(law, magma) for law in conclusion):
                return magma
            solver.add_clause([-F[d][f[d]] for d in range(n)])
    return None


def _search_translation_invariant(job: tuple[list[Equation], list[Equation], Group]) -> Magma | None:
    return find_translation_invariant(*job)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Refute the unconfirmed implications and open questions of an exploration "
                    "with linear and translation-invariant magmas."
    )
    parser.add_argument("results", type=Path, metavar="RESULTS_DIR", help="the results of an exploration")
    parser.add_argument("--equations", type=Path, required=True, metavar="FILE", help="the laws it explored")
    parser.add_argument("--max-modulus", type=int, default=50, metavar="N",
                        help="linear magmas over Z/n for n < N (default 50)")
    parser.add_argument("--matrices", nargs="*", default=["2:2", "2:3"], metavar="K:M",
                        help="linear magmas x*y = Ax + By with k x k matrices over Z/m (default 2:2 2:3)")
    parser.add_argument("--translation-invariant-size", type=int, default=20, metavar="N",
                        help="translation-invariant magmas of sizes up to N (default 20; 0 skips them)")
    parser.add_argument("--groups-order", type=int, default=0, metavar="N",
                        help="translation-invariant magmas x*y = x f(x^-1 y) on the non-cyclic groups "
                             "of small_groups of order up to N (default 0, none)")
    parser.add_argument("-o", "--output", type=Path, metavar="TABLES",
                        help="write the refuting magmas here, one table per line")
    args = parser.parse_args(argv)

    equations = {eq.id: eq for eq in ETP.load_equations(args.equations)}
    implications = json.loads((args.results / "implications.json").read_text(encoding="utf-8"))
    questions = [(i, [equations[n] for n in i["premise"]], [equations[n] for n in i["conclusion"]])
                 for i in implications if i["source"] in ("unconfirmed", "open")]
    refuted: dict[int, Magma] = {}

    def record(magma: Magma, satisfied: frozenset[int]) -> None:
        for k, (_, premise, conclusion) in enumerate(questions):
            if k in refuted or not {eq.id for eq in premise} <= satisfied:
                continue
            if not {eq.id for eq in conclusion} <= satisfied:
                refuted[k] = magma

    rows = set()
    matrix_rings = [tuple(map(int, spec.split(":"))) for spec in args.matrices]
    for linear in linear_magmas(args.max_modulus, matrix_rings):
        satisfied = frozenset(eq.id for eq in linear.satisfied(equations.values()))
        if satisfied not in rows:
            rows.add(satisfied)
            record(linear.magma(), satisfied)
    print(f"Linear magmas: {len(rows)} distinct rows, {len(refuted)} of {len(questions)} questions refuted")

    # Size by size, so that the small sizes are searched for every question first.
    groups = [cyclic(n) for n in range(2, args.translation_invariant_size + 1)]
    groups = sorted(groups + small_groups(args.groups_order), key=lambda g: g.order)
    with ProcessPoolExecutor() as pool:
        for group in groups:
            unrefuted = [k for k in range(len(questions)) if k not in refuted]
            jobs = [(questions[k][1], questions[k][2], group) for k in unrefuted]
            for magma in pool.map(_search_translation_invariant, jobs):
                if magma is not None:
                    record(magma, frozenset(m for m, eq in equations.items() if eq.holds_in_magma(magma)))
            print(f"Translation-invariant magmas on {group.name}: {len(refuted)} of {len(questions)} "
                  f"questions refuted", flush=True)

    for k, magma in sorted(refuted.items()):
        implication, premise, conclusion = questions[k]
        violated = [eq.id for eq in conclusion if not eq.holds_in_magma(magma)]
        if not violated or not all(eq.holds_in_magma(magma) for eq in premise):
            raise AssertionError(f"{magma.name} does not refute {implication}")
        print(f"{implication['source']} {', '.join(f'Eq{eq.id}' for eq in premise)} -> ... "
              f"refuted by {magma.name} (size {magma.size}), violating "
              f"{', '.join(f'Eq{n}' for n in violated)}")
    if args.output is not None:
        tables = {magma.table: magma for magma in refuted.values()}
        args.output.write_text("".join(f"Table {json.dumps([list(row) for row in table])}\n" for table in tables),
                               encoding="utf-8")


if __name__ == "__main__":
    main()
