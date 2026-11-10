# Conceptual Exploration

[![Python Version](https://img.shields.io/badge/python-3.11%2B-blue.svg)](https://www.python.org/downloads/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](https://opensource.org/licenses/MIT)

**`conceptual-exploration`** is a Python library for interactive knowledge discovery and formal theory building based on **Formal Concept Analysis (FCA)**. It provides implementations of:

- **Attribute Exploration** — discovering the canonical (Duquenne–Guigues) implication basis for propositional attributes through interactive expert queries and counterexample refutations.
- **First-Order Rule Exploration** — extending attribute exploration to relational and first-order domains with predicates, typed/sorted variables, and automated symmetry/substitution reductions.

---

## Table of Contents

- [Key Features](#key-features)
- [Background: Formal Concept Analysis](#background-formal-concept-analysis)
- [Installation](#installation)
- [Architecture & Core Concepts](#architecture--core-concepts)
- [Quick Start](#quick-start)
  - [1. Attribute Exploration](#1-attribute-exploration)
  - [2. First-Order Rule Exploration](#2-first-order-rule-exploration)
  - [3. Loading Formal Contexts from `.cxt` Files](#3-loading-formal-contexts-from-cxt-files)
- [Symmetries & Background Knowledge](#symmetries--background-knowledge)
- [Explaining Implications](#explaining-implications)
- [Explorations & Examples](#explorations--examples)
- [Testing](#testing)
- [License](#license)

---

## Key Features

- **NextClosure Algorithm**: Ganter's NextClosure algorithm for lectically ordered enumeration of closed sets and premise candidate generation.
- **Attribute Exploration Engine**: Iterative question-and-answer workflow between the exploration engine and a domain expert/oracle (human, SAT/SMT solver, or dataset).
- **First-Order Rule Exploration (`RuleExploration`)**: Native support for relational signatures, predicates, and sorted variables.
- **Symmetry & Substitution Invariance**: Automatic generation of variable symmetries and variable identification/substitutions to prune redundant queries and map learned implications.
- **Partial Formal Contexts**: First-class handling of three-valued logic (positive, negative, and unknown attribute values) via `PartialContext` and `PartialObject`.
- **Burmeister `.cxt` Format Support**: Read and parse standard Formal Concept Analysis context files.
- **Implication Theory Management**: Simplification of implication premises, entailment checks, semantic closure computations, and source tracking (confirmed, unconfirmed, background, mapped, mapped unconfirmed).
- **Explanations**: For an implication that follows from a set of implications, a minimal subset that entails it and a step-by-step derivation from that subset.

---

## Background: Formal Concept Analysis

**Attribute Exploration** (Bernhard Ganter, 1984) is a semi-automated knowledge acquisition technique in Formal Concept Analysis. Given a set of attributes and a domain of interest:
1. The exploration engine proposes hypothetical implications of the form $P \to C$ (premise implies conclusion).
2. A domain **Expert** evaluates the implication:
   - If the implication is valid, the expert confirms it and it is added to the implication basis.
   - If invalid, the expert provides a **counterexample** (an object that satisfies $P$ but violates at least one attribute in $C$).
3. The process terminates with a minimal, complete implication basis that describes the domain without asking redundant questions.

**Rule Exploration** generalizes this paradigm from propositional attributes to first-order Horn-like relational rules over predicates and variables.

---

## Installation

### Requirements
- Python >= 3.11

### Basic Installation

Clone the repository and install in editable mode:

```bash
git clone https://github.com/username/conceptual-exploration.git
cd conceptual-exploration
pip install -e .
```

### Optional Dependencies

Install extra dependencies for development, tests, or examples:

```bash
# For running tests
pip install -e ".[test]"

# For development (pytest, z3-solver)
pip install -e ".[dev]"

# For examples and Jupyter notebooks (z3-solver, jupyter)
pip install -e ".[examples]"
pip install python-sat
```

The `[test]` extra covers the whole suite, including both domain explorations.
The `[examples]` extra does not pull in `python-sat`, hence the separate install
above for running the Sudoku examples and notebooks.

---

## Architecture & Core Concepts

```
conceptual-exploration/
├── src/conceptual_exploration/       # Core domain-agnostic FCA library
│   ├── algorithms/
│   │   ├── closure.py                # Abstract ClosureOperator protocol
│   │   └── next_closure.py           # NextClosure lectic enumeration algorithm
│   ├── core/
│   │   ├── bitset.py                 # AttributeIndex numbering attributes as bitmask positions
│   │   ├── context.py                # PartialObject and PartialContext (with CXT parser)
│   │   ├── implication.py            # Implication dataclass and respectedness checks
│   │   ├── theory.py                 # ImplicationTheory for closure & simplification
│   │   └── truth.py                  # Truth values a mapping may send an attribute to
│   ├── experts/
│   │   └── base.py                   # Abstract Expert interface (validate method)
│   ├── exploration/
│   │   ├── base.py                   # ExplorationBase with context, mappings & implications
│   │   ├── basis.py                  # Rule and simplified_rules: accepted implications simplified for reading
│   │   ├── attribute.py              # AttributeExploration coordinator
│   │   ├── rule.py                   # RuleExploration first-order coordinator
│   │   └── state.py                  # ExplorationState tracking queries and statistics
│   └── logic/
│       ├── atom.py                   # Atom, GroundedAtom, and atoms_over generator
│       ├── predicate.py              # Predicate, EvaluatablePredicate, and Notation
│       ├── symmetries.py             # Variable permutations and substitutions
│       └── variable.py               # Variable, SortedVariable, and Sort enum
├── explorations/                     # Domain exploration projects and case studies
│   ├── equational_theories/          # Equational Theories Project (ETP) magma exploration
│   │   ├── magma.py                  # Algebraic structures, term ASTs, ETP catalog & MagmaExpert
│   │   ├── explore.py                # Exploration runner script
│   │   ├── explore.ipynb             # Interactive Jupyter notebook
│   │   └── README.md                 # Project background & documentation
│   └── sudoku/                       # Sudoku rule and constraint exploration
│       ├── sudoku.py                 # SAT/SMT models, experts, predicates & symmetries
│       ├── config.py                 # TOML configuration of explorations
│       ├── configs/                  # Shipped exploration configurations
│       ├── explore.py                # Exploration runner script
│       ├── explore.ipynb             # Interactive Jupyter notebook
│       └── README.md                 # Project background & documentation
├── examples/                         # Minimal API examples and interactive demonstrations
└── tests/                            # Unit and integration test suites
```

### Key Classes

| Class | Location | Description |
|---|---|---|
| `AttributeExploration` | `conceptual_exploration` | Orchestrates standard attribute exploration over a set of attributes and an `Expert`. |
| `RuleExploration` | `conceptual_exploration` | Orchestrates first-order rule exploration given predicates, variables, and an `Expert`. |
| `ExplorationBase` | `conceptual_exploration` | Manages attributes, background implications, partial contexts, and symmetry mappings. |
| `Expert` | `conceptual_exploration` | Abstract base class for domain oracles implementing `validate(implication, attributes)`. |
| `QuestionReport` / `report_every` | `conceptual_exploration` | Per-question progress event emitted by an exploration, and a ready-made callback printing every nth one. |
| `Implication` | `conceptual_exploration` | Represents a rule of the form $\text{Premise} \to \text{Conclusion}$. |
| `ImplicationTheory` | `conceptual_exploration` | Maintains a set of implications, computes closures, checks entailment, and simplifies rules. |
| `Rule` / `simplified_rules` | `conceptual_exploration` | The accepted implications as non-redundant rules, with premises and conclusions cut to what the background, the other rules and the mappings do not already give. |
| `PartialObject` | `conceptual_exploration` | Represents a concrete or counterexample object with `positive` and `negative` attribute sets. |
| `PartialContext` | `conceptual_exploration` | Formal context storing objects and attributes, capable of loading `.cxt` files. |
| `Predicate` / `EvaluatablePredicate` | `conceptual_exploration` | Relational symbol with fixed arity, sort constraints, declared properties, and optional evaluation function. |
| `Variable` / `SortedVariable` | `conceptual_exploration` | Variables used in first-order relational atoms. |
| `Magma` / `MagmaExpert` | `explorations.equational_theories` | Finite Cayley table representation and oracle for Equational Theories Project (ETP) exploration. |
| `Equation` / `Term` | `explorations.equational_theories` | AST for algebraic magma equations and terms with duality symmetry transformations. |
| `ETP` | `explorations.equational_theories` | Equational Theories Project catalog with curated equation sets and duality mappings. |

---

## Quick Start

### 1. Attribute Exploration

Here is a minimal example discovering arithmetic relationships over small integers:

```python
from conceptual_exploration import simplified_rules
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.attribute import AttributeExploration
from conceptual_exploration.exploration.base import ExplorationBase


class NamedPredicate:
    def __init__(self, name, predicate):
        self.name = name
        self.predicate = predicate

    def __call__(self, n):
        return self.predicate(n)

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def __lt__(self, other):
        return self.name < other.name


class IntegerExpert(Expert):
    def __init__(self, domain, predicates):
        self.domain = domain
        self.predicates = predicates

    def validate(self, implication, attributes=None):
        for n in self.domain:
            # Check if integer n satisfies the premise but violates conclusion
            if all(p(n) for p in implication.premise) and any(not c(n) for c in implication.conclusion):
                positives = {p for p in self.predicates if p(n)}
                negatives = set(self.predicates) - positives
                return PartialObject(n, positives, negatives)
        return None  # Implication holds across domain


attributes = [
    NamedPredicate("even", lambda n: n % 2 == 0),
    NamedPredicate("odd", lambda n: n % 2 == 1),
    NamedPredicate("divisible_by_4", lambda n: n % 4 == 0),
    NamedPredicate("divisible_by_6", lambda n: n % 6 == 0),
]

base = ExplorationBase(attributes=attributes)
expert = IntegerExpert(domain=range(1, 100), predicates=attributes)
exploration = AttributeExploration(base, expert)

exploration.run()

print("Discovered Implications:")
for rule in simplified_rules(base):
    print(f"  {rule}")
```

An exploration runs silently by default. To watch it work, pass a callback — `report_every(n)` prints every nth question together with the expert's verdict:

```python
from conceptual_exploration import report_every

exploration = AttributeExploration(base, expert, on_question=report_every(20))
```

The callback receives a `QuestionReport` carrying the question number, the implication asked, the counterexample (or `None` when accepted), the resulting `ImplicationSource`, and the size of the theory at that moment. Any other rendering — a progress bar, a log record, a CSV row — is a matter of passing a different callable. `RuleExploration` takes the same `on_question` argument.

### 2. First-Order Rule Exploration

Explore relational rules over variables $x, y, z$ and binary order/equality predicates:

```python
from itertools import product
from conceptual_exploration import simplified_rules
from conceptual_exploration.core.context import PartialObject
from conceptual_exploration.experts.base import Expert
from conceptual_exploration.exploration.rule import RuleExploration
from conceptual_exploration.logic.predicate import EvaluatablePredicate, Notation
from conceptual_exploration.logic.variable import Variable


class NumberRelationalExpert(Expert):
    def __init__(self, domain, variables):
        self.domain = tuple(domain)
        self.variables = variables

    def validate(self, implication, attributes=None):
        for values in product(self.domain, repeat=len(self.variables)):
            assignment = dict(zip(self.variables, values))
            # Verify premise holds for assignment
            if all(atom(assignment).holds() for atom in implication.premise):
                for atom in implication.conclusion:
                    if not atom(assignment).holds():
                        positive = {a for a in implication.premise}
                        return PartialObject(tuple(assignment.items()), positive, {atom})
        return None


predicates = [
    EvaluatablePredicate("<", 2, function=lambda a, b: a < b, notation=Notation.INFIX),
    EvaluatablePredicate("=", 2, function=lambda a, b: a == b, notation=Notation.INFIX),
]
variables = [Variable("x"), Variable("y"), Variable("z")]

expert = NumberRelationalExpert(domain=range(-5, 6), variables=variables)
exploration = RuleExploration(predicates, variables, expert, substitutions=True)
exploration.run()

rules = simplified_rules(exploration.base)
print(f"Discovered {len(rules)} first-order rules:")
for rule in rules:
    print(f"  {rule}")
```

### 3. Loading Formal Contexts from `.cxt` Files

You can initialize contexts from standard Burmeister `.cxt` files:

```python
from conceptual_exploration.core.context import PartialContext

# Load context from file
context = PartialContext.from_cxt("examples/test.cxt")

print(f"Loaded {len(context.objects)} objects and {len(context.attributes)} attributes.")
```

---

## Symmetries & Background Knowledge

In many domains, rules are invariant under symmetries (e.g. geometric rotations, renaming of symmetric variables, or digit permutations in Sudoku). 

`conceptual-exploration` allows passing mappings/symmetries to `ExplorationBase`:
- Whenever an implication is accepted, its symmetric transformations are automatically derived and accepted without asking the expert.
- Whenever a counterexample is provided, its symmetric counterparts are generated in the background context.

```python
base = ExplorationBase(
    attributes=attributes,
    background_implications=background_rules,
    mappings=symmetry_mappings,
)
```

For first-order rule exploration, variable symmetries (permutations and non-injective variable substitutions) are configured automatically via `substitutions=True` in `RuleExploration`.

A binary predicate can declare itself `symmetric`, `reflexive` or `irreflexive`, and name its `complement`. `RuleExploration` then keeps one atom of each symmetric pair, drops atoms whose truth is fixed, such as `P(x, x)` for a reflexive `P`, and adds `{P(a), Q(a)} -> ⊥` for complementary predicates.

---

## Explaining Implications

When an implication `P -> Q` follows from a set `L` of implications, `explain(P, Q, L)` in `conceptual_exploration.algorithms.explanation` says why: it returns a **minimal** subset `K` of `L` that entails `P -> Q`, and a **derivation** of `P -> Q` from `K`, a sequence of steps each applying one implication of `K` whose premise is already known. It returns `None` if `L` does not entail `P -> Q`.

```python
from conceptual_exploration import Implication
from conceptual_exploration.algorithms.explanation import explain

L = [Implication("a", "b"), Implication("a", "e"), Implication("b", "d"), Implication("e", "cd")]
for step in explain("a", "cd", L).steps:
    print(step.implication, "gives", sorted(step.derived))
# a -> e gives ['e']
# e -> c, d gives ['c', 'd']
```

The idea, in three steps, all in polynomial time:

1. **Forward chaining with provenance.** The closure of `P` under `L` is computed as usual, but each attribute added records the step that added it. As in the LinClosure algorithm of Beeri and Bernstein, each implication keeps a counter of its premise attributes not yet known, and fires when the counter reaches zero, so the closure takes time linear in the size of `L`. Implications fire first in, first out, so that what needs fewer steps is derived first.
2. **Going backwards from `Q`.** From the attributes of `Q`, the records lead back to the steps they need, then to the steps the premises of those need, and so on. These steps, in their order, are a derivation of `P -> Q` (a derivation DAG in the sense of Maier's *Theory of Relational Databases*), and their implications a subset of `L` that entails it.
3. **Deleting what is not needed.** That subset need not be minimal: an attribute may have been derived on a route the rest does not need, as `d` by `a -> b` and `b -> d` in the example above, before `e -> c, d` fired. Each implication of the subset is therefore deleted in turn, the last steps first, and kept out if `P -> Q` still follows. Since entailment is monotone, the result is minimal: no implication can be removed from it. Deriving `P -> Q` once more from it gives the derivation returned.

The subset is minimal, not of minimum size: finding a smallest one is NP-hard, and there can be exponentially many minimal ones (Baader, Peñaloza and Suntisrivaraporn, *Pinpointing in the description logic EL+*, 2007; Peñaloza and Sertkaya, *On the complexity of axiom pinpointing in the EL family of description logics*, 2010). Which one is found depends on the order of deletion. The problem is known as *axiom pinpointing* or finding *justifications* in description logics, and as finding *minimal unsatisfiable subsets* for Horn formulas in SAT; derivations that are small or shallow are the subject of work on *good proofs* (Alrabbaa, Baader, Borgwardt, Koopmann and Kovtunova, 2020–2021).

`explorations/equational_theories/explain.py` applies this to the implications an exploration accepted, and prints each step with the source of its implication.

---

## Explorations & Examples

### Domain Explorations (`explorations/`)

The `explorations/` directory houses specialized mathematical and domain-specific exploration projects:

- **`explorations/equational_theories/`**: Conceptual exploration of equational laws on magmas from the **Equational Theories Project (ETP)**. Combines term ASTs, Cayley table models, and duality symmetry mappings with one of two experts: `MagmaExpert`, which searches for a finite counterexample with the Z3 SMT solver and marks an implication `UNCONFIRMED` when its per-size solver budget (`z3_timeout_ms`) runs out, and `VampireExpert`, which proves implications with the Vampire theorem prover and refutes them with finite counterexamples of any size or with free magmas. Includes a standalone runner (`explore.py`) and an interactive Jupyter notebook (`explore.ipynb`).
- **`explorations/sudoku/`**: Conceptual exploration of Sudoku rules and constraints. Combines SAT-based propositional exploration with PySAT and the symmetry group of the grid (line and band permutations, transposition, digit permutations), first-order relational rule exploration with a PySAT or Z3 expert over multi-sorted variables (`SudokuSort.CELL` and `SudokuSort.NUMBER`), and the exploration of deduction rules on partial grids, including a runner (`explore.py`) driven by TOML configurations and an interactive Jupyter notebook (`explore.ipynb`).

### Lightweight Examples (`examples/`)

The `examples/` directory contains focused demonstrations of core library features:

- `numbers_exploration.py`: Propositional exploration of prime numbers, factorials, parity, and divisibility.
- `numbers_rule_exploration.py`: First-order exploration of arithmetic inequalities and signs.
- `simulated_exploration.py`: Automated benchmarking and simulated exploration over existing `.cxt` formal contexts.
- `implication_theories_exploration.py`: Meta-exploration of implication theories and inference rules.

---

## Testing

Run the test suite using `pytest`:

```bash
pytest
```

Or using Python directly:

```bash
PYTHONPATH="src:." python3 -c "import tests.test_enumerator as t, tests.test_magma as m, tests.test_sudoku as s; t.test_next_closure_one(); t.test_next_closure_complete(); m.test_term_parsing_and_eval(); m.test_magma_attribute_exploration(); s.test_sudoku2sat_and_solve_4x4(); s.test_sudoku_expert_sat(); print('All tests passed!')"
```

---

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.
