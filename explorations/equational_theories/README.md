# Equational Theories Project (ETP) — Magma Exploration

This exploration project applies Formal Concept Analysis (FCA) and Attribute Exploration to the **Equational Theories Project (ETP)**.

## Background

The **Equational Theories Project (ETP)** explores the complete landscape of implications and non-implications among equational laws on magmas (sets equipped with a single binary operation $*$).

Given a signature with binary operation $*$ and variables $x, y, z, \dots$, an equational law $L = R$ is an identity universally quantified over all occurring variables. Examples include:
- **Commutativity (Eq 43)**: $x * y = y * x$
- **Associativity (Eq 4512)**: $(x * y) * z = x * (y * z)$
- **Idempotence (Eq 3)**: $x = x * x$
- **Medial / Entropic**: $(x * y) * (z * w) = (x * z) * (y * w)$
- **Steiner Law 1 (Eq 16)**: $x * (x * y) = y$

## Features

- **AST Representation & Evaluation**: Expressive term trees (`Term`, `Var`, `Op`) and equations (`Equation`) evaluated against finite Cayley tables.
- **Duality Symmetries**: Anti-automorphism mappings $(x * y)^{\text{op}} = y^{\text{op}} * x^{\text{op}}$ integrated into `ExplorationBase` to reduce redundant expert queries by up to 50%.
- **Automated Counterexample Oracle (`MagmaExpert`)**: Checks candidate implications against a catalog of standard finite magmas (cyclic groups, projections, tournaments, boolean magmas), then searches for a counterexample Cayley table with the **Z3 SMT solver**, representing the operation as an uninterpreted function over the finite domain of each candidate size $n$.
- **Theorem-Proving Oracle (`VampireExpert`)**: Proves implications in equational logic with the Vampire theorem prover and refutes them with finite counterexamples of any size or with free magmas over the premise, which are usually infinite.
- **Unconfirmed Results**: An implication the expert could neither refute nor prove, because Z3's per-size solver budget ran out or Vampire found neither a proof nor a counterexample in its time limits, is accepted but reported `[UNCONFIRMED]` instead of being presented as verified; Vampire rejects it instead when it shows the implication false without a counterexample.
- **Rules**: Simplifies the implications found into rules for reading, with premises and conclusions cut to what the background, duality and the other rules do not give, and drops the rules that are then redundant.

## Quick Start

Run the exploration script:

```bash
python explorations/equational_theories/explore.py
```

The equations explored as attributes are listed in [`equations.json`](equations.json); each entry has an `equation` string and optional `name` and `id` fields, and the set must be closed under duality, unless `--no-duality` is given. `--axiom LAW...` (ETP ids or names among the equations) makes laws hold in every object: for semigroups, `--axiom 4512`, with [`equations_semigroup.json`](equations_semigroup.json): the first law of each ETP class of the 653 right-associated laws of order at most 4, the reversals of these laws, and associativity, 248 laws written by `etp.py equations.txt --max-order 4 --graph graph.json --semigroup` (preset [`configs/semigroup.toml`](configs/semigroup.toml)). For commutative semigroups, `--axiom 4512 43` with [`equations_csemigroup5.json`](equations_csemigroup5.json): the semigroup laws of order at most 5 in commutative form, of order at most 4 one for each class of laws equivalent among semigroups, written with [`background_csemigroup5.json`](background_csemigroup5.json), the theory of the order-4 semigroup exploration, and [`seeds_csemigroup5.json`](seeds_csemigroup5.json), the commutative semigroups of at most five elements and monomial semigroups of at most 32, by `semigroup.py commutative-inputs` (preset [`configs/csemigroup5.toml`](configs/csemigroup5.toml)). For semigroups of order at most 5, [`equations_semigroup5.json`](equations_semigroup5.json): one law of each of the 380 classes of the 3,284 semigroup laws of order at most 5, closed under reversal, the classes found by `semigroup.py classes` (results in `results/semigroup_order5_classes`), with [`background_semigroup5.json`](background_semigroup5.json), the theory of the order-4 semigroup exploration, and [`seeds_semigroup5.json`](seeds_semigroup5.json), the semigroups of at most four elements, those of the order-4 exploration, monomial semigroups and the Heisenberg groups over Z3 and Z5, written by `semigroup.py inputs` (preset [`configs/semigroup5.toml`](configs/semigroup5.toml)). Seeded magmas violating an axiom are dropped, and with associativity among the axioms laws are dual when their words, read without parentheses, are reversed. Use `--equations` to explore a different file:

```bash
python explorations/equational_theories/explore.py --equations my_equations.json
```

The per-magma-size solver budget is configurable with `--z3-timeout-ms` (default `30000`; `0` or less runs unbounded):

```bash
python explorations/equational_theories/explore.py --z3-timeout-ms 500
```

A tighter budget trades unconfirmed implications for speed rather than changing the answer: a query that runs out of time is reported `[UNCONFIRMED]` instead of being decided, so a smaller budget finishes sooner and leaves more implications unproved. Running unbounded removes the flagging entirely, at the cost of a few pathological searches at the larger magma sizes, which can dominate the running time.

The solver searches for counterexample magmas of sizes `--min-search-size` to `--max-search-size` (defaults `1` and `6`); the built-in pool of small standard magmas is checked first regardless:

```bash
python explorations/equational_theories/explore.py --min-search-size 4 --max-search-size 7
```

Progress reporting is controlled with `--report-every` (default `1`, showing every question the expert is asked; `0` or less prints nothing):

```bash
python explorations/equational_theories/explore.py --report-every 1
```

With `--expert vampire`, questions the pool does not refute go to the [Vampire](https://vprover.github.io) theorem prover (installed separately, e.g. `brew install vampire`). It tries to prove the implication on all cores (`--vampire-first-time-limit`, by default the proving time limit `--vampire-prove-time-limit`, `10` seconds; 3 are enough) and then, briefly, to find a counterexample of any size (`--vampire-quick-model-time-limit`, default `1`). Failing both, it decides each law on its own, except those the premise implies by the background and the implications proved so far, for the free magma over the premise (`--vampire-row-time-limit` seconds per law outside the conclusion, by default the proving time limit; `0` leaves them unknown), whose elements are terms modulo the equations the premise derives: that magma, usually infinite, refutes the implication when a law of the conclusion is not derivable, and the implication is proved when every law of the conclusion is. Otherwise it searches for counterexamples again, to each law of the conclusion not proved, separately and on all cores (`--vampire-model-time-limit` seconds per law, default `10`), and so does the [Mace4](https://www.cs.unm.edu/~mccune/prover9/) model finder with `--mace4-time-limit S` (default `0`, not used; installed separately, e.g. `brew install prover9`), which sweeps the sizes: each Mace4 search is for one law at one size, a core that finishes one takes the smallest size not yet started, and the sweep gets `S` seconds in all. Each model found joins the pool and stops the searches for the laws it violates; the others go on until every law is violated or the time is up, so that the pool answers the next questions about the premise, and a law whose search ran out of time is not searched for again with that premise. With `--truncation-words W` and associativity among the axioms, the truncated free semigroups of the premise's variety, of at most `W` words ([`free_semigroup.py`](free_semigroup.py)), are tried first, for 30 seconds at most: they refute laws whose countermodels are too large for the model searches. With `--model-premise simplified`, the searches use a subset of the premise whose closure under the background and the implications proved is the premise (laws every object satisfies, such as `--axiom` laws, are kept); `both` searches both; models are checked against the full premise. With `--eprover-time-limit S` (default `0`, not used; installed separately, e.g. `brew install eprover`), the [E](https://eprover.org) prover first decides each law of the conclusion in the free magma's row, and Vampire only the laws it leaves; 2 seconds are enough. With `--prover9-time-limit S` (default `0`, not used; it comes with Mace4), [Prover9](https://www.cs.unm.edu/~mccune/prover9/) then tries to prove each law E leaves, before Vampire; only its proofs count. The row is completed with the known implications: what the laws proved imply is proved too, and a law that would imply a refuted one is refuted. The laws of the conclusion it proves are then accepted; the rest is rejected if Vampire shows the implication false (if only one law is left, the free magma over the premise refutes it instead), and accepted as `[UNCONFIRMED]` otherwise, unless the theory would then entail a rejected implication, in which case it is not accepted but reported as conflicting. Objects are completed only with background and confirmed implications. The dual of an unconfirmed implication is labelled `mapped unconfirmed`; with `--ask-unconfirmed-duals`, it is not added to the theory until the implication is confirmed, so that it does not steer the enumeration, and its question is asked in turn. When a later object refutes an unconfirmed implication, which has steered the enumeration since it was accepted, the exploration resumes at the question it was accepted at, keeping what was accepted before, the confirmed implications found after, and every object; the refuted implication is reported and dropped. The search sizes and solver budget above apply to the default `z3` expert only:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --expert vampire
```

With `--expert completion`, meant for one-variable laws, each question's premise is completed into a convergent rewrite system by Knuth–Bendix completion: the implication is proved if the sides of every law of its conclusion have the same normal form, and refuted otherwise by the free magma over the premise, whose row the normal forms decide completely and certify. Questions whose premise cannot be completed go to Vampire if it is installed. For the 31 one-variable laws of order at most four, completion decides every question, in minutes:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --expert completion
```

With `--background-order N`, implications derivable by equational reasoning are given to the exploration as background knowledge (one-variable equations only). The rules are multiplying both sides by the same term from the same side, substituting a term for the variable, and replacing a subterm by an equivalent one, applied through equations of at most `N` operations. `--background-premise-size K` (default `2`) bounds their premises; `0` computes the canonical basis of everything derivable instead, which is slower. `--background-transient-order M` lets a single multiplication or substitution reach equations of up to `M` operations, as long as rewriting with derived equations brings the result back within `N`:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --background-order 4 --background-transient-order 10
```

With `--etp-graph PATH --etp-equations PATH`, the implications between two of the explored laws that the [ETP](https://github.com/teorth/equational_theories) decided are given to the exploration as background knowledge, so that it asks only about premises of several laws. The two files are the ETP's [implication graph](https://teorth.github.io/equational_theories/implications/graph.json) and its [list of laws](https://github.com/teorth/equational_theories/blob/main/data/equations.txt), by which the explored laws are matched whatever their variables; an `id` must be the ETP's number of the law. `etp.py` writes chosen ETP laws, with their duals, as an equations file:

```bash
python explorations/equational_theories/etp.py equations.txt 3 43 4512 -o my_laws.json
python explorations/equational_theories/explore.py --equations my_laws.json --expert vampire --etp-graph graph.json --etp-equations equations.txt
```

With `--etp-refutations` as well, each implication between two of the explored laws that the ETP refutes is added to the context as an object that satisfies its premise and the laws the premise implies and violates its conclusion and the laws implying it, which covers the ETP's infinite counterexamples; refutations accounted for by the other objects are dropped, and the rest saved in `etp_refutations.json`.

With `--max-order K --graph graph.json` instead of numbers, it writes one law of each class of ETP laws of at most `K` operations that imply each other, closed under duality, each with the members of its class; [`equations_order2.json`](equations_order2.json) and [`equations_order3.json`](equations_order3.json) were written so, from the ETP data recorded in [`etp_version.json`](etp_version.json). `fetch_etp.py DIR` downloads that data into `DIR`, checking each file against its recorded checksum: `equations.txt` and `graph.json`, and the ETP's files of finite magmas in `DIR/magmas`. The fourth exploration of the laws of order at most three, for instance, was run as

```bash
python explorations/equational_theories/fetch_etp.py etp
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_order3.json --expert vampire --vampire-row-time-limit 1 --mace4-time-limit 30 --etp-graph etp/graph.json --etp-equations etp/equations.txt --etp-refutations --ask-unconfirmed-duals --seed-context etp/magmas/*.txt
```

The rules found for the laws of order at most two are proved in Lean in [`lean/`](lean/README.md). `completion.py RESULTS_DIR --equations FILE` certifies the negative entries of an exploration's free magmas, which rest on Vampire's saturation, by Knuth–Bendix completion: a terminating, confluent rewrite system that entails the premise and separates the two sides of a law shows that the premise does not imply it.

`explain.py RESULTS_DIR --equations FILE --premise N ... --conclusion N ...` explains why an implication follows from the implications an exploration accepted: it finds a minimal set of them that entails it and derives it step by step, each step applying one of them, with its source (`conceptual_exploration.algorithms.explanation`). Only the implications that hold are used, unless `--unconfirmed` is given. For example, Eq127 and Eq310 together imply Eq387, though neither does alone, by 10 of the 1645 implications of the fourth order-3 exploration:

```bash
python explorations/equational_theories/explain.py explorations/equational_theories/results/order3_vampire_mace4_etp_refutations_duals_asked --equations explorations/equational_theories/equations_order3.json --premise 127 310 --conclusion 387
```

Magmas found earlier, such as the `magmas.json` of saved results, can be reused. Files of the ETP with one table per line, such as those in its `equational_theories/Generated/All4x4Tables/data`, are read as well. `--seed-magmas PATH...` adds them to the expert's pool, which is checked for a counterexample before the solver searches. `--seed-context PATH...` instead evaluates them on every equation and adds them to the context before the exploration starts, dropping those whose rows the others account for, so that no question they refute is asked. `--background PATH...` adds the implications of files in the format of `implications.json` to the background:

```bash
python explorations/equational_theories/explore.py --equations explorations/equational_theories/equations_1var_order4.json --seed-context explorations/equational_theories/results/1var_order4_sizes1-6/magmas.json
```

Options can also be read from a TOML file with `--config FILE`, keyed by option name without the dashes, the command line overriding it; paths are relative to the directory `explore.py` is run from, and patterns such as `etp/magmas/*.txt` are expanded. [`configs/order3.toml`](configs/order3.toml) holds the settings for the laws of order at most three:

```bash
python explorations/equational_theories/explore.py --config explorations/equational_theories/configs/order3.toml
```

Each run saves its options, with the commits of the repository and of the ETP data, as `settings.toml`, so that `--config RESULTS_DIR/settings.toml` runs it again, and its log (`exploration.log`), the implications found, each with its source (`implications.txt`, `implications.json`) together with the rejected implications, everything found simplified into rules, each with its provenance: the background, simplified the same way, and the rules printed at the end, each followed by its dual, with each law written out, as words for semigroups (`simplified_implications.txt`), and its context (`magmas.json`, `free_magmas.json`, `etp_refutations.json`, `context.cxt` with the objects whose rows are complete, and `partial_context.cxt` with every object, `?` marking the equations not known to hold or fail) to a new directory under `results/` named after the equations file and the starting time, or to `--results-dir PATH`.

Or open the interactive Jupyter notebook:

```bash
jupyter notebook explorations/equational_theories/explore.ipynb
```
