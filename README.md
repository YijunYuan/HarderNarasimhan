# HarderNarasimhan

![CI](https://github.com/YijunYuan/HarderNarasimhan/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-db584cd6d46c92f209a44c0f1c829460d327499d-5C2D91)](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

[![Graph](https://img.shields.io/badge/Dependency_graph-100000?style=for-the-badge&logo=GitHub&logoColor=white&labelColor=black&color=black)](https://yijunyuan.github.io/lean-graph/?url=https://raw.githubusercontent.com/YijunYuan/HarderNarasimhan/refs/heads/literal/HarderNarasimhan.json#dark)

A Lean 4 formalization of the **Harder–Narasimhan Games** of Huayi Chen & Marion Jeannin: a two-player game played on the
strict intervals of a bounded lattice. The library develops Harder–Narasimhan filtrations,
Jordan–Hölder filtrations, and coprimary filtrations of nonzero finitely generated modules
over a Noetherian commutative ring.

This branch follows the original paper as faithfully as possible, separating definitions,
statements, and proofs so that the formalization can be read alongside the text. For a
version organized for easier use as a library, see the
[`master` branch](https://github.com/YijunYuan/HarderNarasimhan/tree/master).

## Mathematical overview

The central object is a *payoff function*: a bundled structure

```lean
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  toFun : StrictIntvl ℒ → S
```

assigning to each strict interval `(a, b)` (with `a < b`) of an order `ℒ` a payoff in a
complete lattice `S`. The main definitions use dot notation on `μ`:

- `μ.max I` — the supremum over `I.left < u ≤ I.right`, with the left endpoint fixed;
- `μ.min I` — the infimum over `I.left ≤ u < I.right`, with the right endpoint fixed;
- `μ.A I` / `μ.B I` — the game values when player A or player B moves first, respectively;
- `μ.restrict I` — the induced payoff function on the points `↥I` of a subinterval;
- `μ.dual` — the order-dual payoff function, exchanging the two players;
- `μ.IsConvex`, `μ.IsSlopeLike`, `μ.IsSemistable`, … — typeclass hypotheses on `μ`;
- `μ.breakpoints I` — the canonical cut points from which filtrations are built;
- `μ.HarderNarasimhanFiltration` — the type of Harder–Narasimhan filtrations of `μ`.

Under suitable chain and slope-like conditions, the game values satisfy
`μ.A ⊤ = μ.min ⊤` and `μ.B ⊤ = μ.max ⊤`. For linearly ordered slope-like payoffs satisfying `WeakACC` and `StrongDCC`,
Nash equilibrium is equivalent to semistability. For convex admissible payoffs satisfying the ascending chain condition and
`ADCC`, iterating greatest breakpoints gives a Harder–Narasimhan filtration, unique when
the payoff order is linear. Applying this construction to associated primes of subquotients
gives coprimary filtrations, relative to a fixed linear extension of the prime spectrum.

## Reading alongside the paper

The chapter layout and numbering follow Chen–Jeannin,
[*Harder–Narasimhan Games*, arXiv:2306.08283v1](https://arxiv.org/abs/2306.08283v1).

Each chapter has three files:

- `Defs.lean` — definitions, hypothesis classes, and the essential coercion/structure API.
- `Impl.lean` — constructions, auxiliary lemmas, and proofs, collected in the
  `HarderNarasimhan.Impl` namespace.
- `Results.lean` — concise numbered statements in paper order, proved from `Impl`.

Import `HarderNarasimhan` for the whole library, or a chapter's `Results` for its public entry point.
Numbered entry points such as `HarderNarasimhan.theorem_3_10` live in the
`HarderNarasimhan` namespace. Definitions live in their corresponding namespaces in `Defs`,
while implementation declarations are kept under `HarderNarasimhan.Impl`.
Definitions and results have docstrings identifying the corresponding paper item. Technical
lemmas are labelled as auxiliary results for that item; unnumbered notions are identified by
section and their related numbered statement.

| Paper section | Definitions | Statements | Proofs |
|---|---|---|---|
| §2.2 Convexity | [Defs](HarderNarasimhan/Convexity/Defs.lean) | [Results](HarderNarasimhan/Convexity/Results.lean) | [Impl](HarderNarasimhan/Convexity/Impl.lean) |
| §3.1 Semistability | [Defs](HarderNarasimhan/Semistability/Defs.lean) | [Results](HarderNarasimhan/Semistability/Results.lean) | [Impl](HarderNarasimhan/Semistability/Impl.lean) |
| §3.3 Harder–Narasimhan filtration | [Defs](HarderNarasimhan/Filtration/Defs.lean) | [Results](HarderNarasimhan/Filtration/Results.lean) | [Impl](HarderNarasimhan/Filtration/Impl.lean) |
| §3.4 Coprimary filtration | [Defs](HarderNarasimhan/CoprimaryFiltration/Defs.lean) | [Results](HarderNarasimhan/CoprimaryFiltration/Results.lean) | [Impl](HarderNarasimhan/CoprimaryFiltration/Impl.lean) |
| §§4.1–4.2 First-mover advantage and duality | [Defs](HarderNarasimhan/FirstMoverAdvantage/Defs.lean) | [Results](HarderNarasimhan/FirstMoverAdvantage/Results.lean) | [Impl](HarderNarasimhan/FirstMoverAdvantage/Impl.lean) |
| §4.3 Slope-like payoffs | [Defs](HarderNarasimhan/SlopeLike/Defs.lean) | [Results](HarderNarasimhan/SlopeLike/Results.lean) | [Impl](HarderNarasimhan/SlopeLike/Impl.lean) |
| §4.4 Nash equilibrium | [Defs](HarderNarasimhan/NashEquilibrium/Defs.lean) | [Results](HarderNarasimhan/NashEquilibrium/Results.lean) | [Impl](HarderNarasimhan/NashEquilibrium/Impl.lean) |
| §4.5 Jordan–Hölder filtration | [Defs](HarderNarasimhan/JordanHolderFiltration/Defs.lean) | [Results](HarderNarasimhan/JordanHolderFiltration/Results.lean) | [Impl](HarderNarasimhan/JordanHolderFiltration/Impl.lean) |

Shared infrastructure remains in [StrictIntvl](HarderNarasimhan/StrictIntvl.lean),
[PayoffFunction/Defs](HarderNarasimhan/PayoffFunction/Defs.lean), and
[PayoffFunction/Restrict](HarderNarasimhan/PayoffFunction/Restrict.lean): strictly ordered pairs,
the game values, and restrictions (Definitions 2.1–2.2 and Notation 4.9).
The commutative algebra input for Proposition 3.12 is in
[CoprimaryFiltration/CommutativeAlgebra](HarderNarasimhan/CoprimaryFiltration/CommutativeAlgebra.lean).

## Numbered results

| Paper item | Entry point in `HarderNarasimhan` |
|---|---|
| Lemma 2.4 | `lemma_2_4` |
| Remarks 2.5, 2.7 | `remark_2_5`, `remark_2_7` |
| Propositions 2.6, 2.8 | `proposition_2_6`, `proposition_2_8` |
| Proposition 3.2; Corollary 3.3 | `proposition_3_2`, `corollary_3_3` |
| Proposition 3.4; Remark 3.5 | `proposition_3_4`, `remark_3_5` |
| Propositions 3.7–3.8 | `proposition_3_7`, `proposition_3_8` |
| Definition 3.9; Theorem 3.10 | `definition_3_9`, `theorem_3_10` |
| Propositions 3.11–3.13 | `proposition_3_11`, `proposition_3_12`, `proposition_3_13` |
| Remark 3.14; Theorem 3.15; Remark 3.16 | `remark_3_14`, `theorem_3_15`, `remark_3_16` |
| Propositions 4.1, 4.3; Remark 4.4 | `proposition_4_1`, `proposition_4_3`, `remark_4_4` |
| Propositions 4.6, 4.8 | `proposition_4_6`, `proposition_4_8` |
| Remark 4.10; Propositions 4.11–4.16 | See [NashEquilibrium/Results](HarderNarasimhan/NashEquilibrium/Results.lean) |
| Propositions 4.18, 4.20; Theorem 4.21 | `proposition_4_18`, `proposition_4_20`, `theorem_4_21` |
| Theorem 4.25; Remark 4.26 | `theorem_4_25`, `remark_4_26` |

Theorem 3.10 identifies every Harder–Narasimhan filtration with the canonical one;
combined with Definition 3.9 this gives the existence and uniqueness of Theorem 1.1.
Theorem 3.15 is Theorem 1.2 from the introduction, and Theorem 4.21 is Theorem 1.3.

Some hypotheses need to be read explicitly alongside v1. The formal Proposition 4.3 uses
the actual order dual of Proposition 4.1: the first disjunct in `WeakSlopeLikeAtBot` is
`μ(⊥, y) ≤ μ(x, y)`, where v1 prints `μ(⊥, x) ≤ μ(x, y)`.
The length result of Remark 4.26 assumes a modular lattice.
The five-way equivalence in Theorem 4.21 uses the global weak ascending and
strong descending chain conditions from the paper; the more general restriction-based
criterion of Proposition 4.20 remains available separately.

## Building

The repository pins Lean and mathlib via [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml):

```bash
lake exe cache get   # fetch the mathlib build cache
lake build
```

## License

Licensed under the Apache License, Version 2.0.  See [LICENSE](LICENSE).

[ChenJeannin]: https://arxiv.org/abs/2306.08283
