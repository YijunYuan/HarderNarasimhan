# HarderNarasimhan

![CI](https://github.com/YijunYuan/HarderNarasimhan/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-v4.33.0-5C2D91)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

[![Graph](https://img.shields.io/badge/Dependency_graph-100000?style=for-the-badge&logo=GitHub&logoColor=white&labelColor=black&color=black)](https://yijunyuan.github.io/lean-graph/?url=https://raw.githubusercontent.com/YijunYuan/HarderNarasimhan/refs/heads/master/HarderNarasimhan.json#dark)

A Lean 4 formalization of the **Harder–Narasimhan game** of Chen–Jeannin
(referenced throughout the source as `[ChenJeannin]`): a two-player game played on the
strict intervals of a bounded lattice, whose optimal strategies recover
Harder–Narasimhan filtrations, Jordan–Hölder filtrations, and — for modules over a
Noetherian ring — the classical coprimary filtrations.

## Mathematical overview

The central object is a *payoff function*: a bundled structure

```lean
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  toFun : StrictIntvl ℒ → S
```

assigning to each strict interval `(a, b)` (with `a < b`) of an order `ℒ` a payoff in a
complete lattice `S`.  Everything else is accessed through dot notation on `μ`:

- `μ.max I` / `μ.min I` — extremal payoffs over interior points of `I`;
- `μ.A I` / `μ.B I` — the first-player (minimax) and second-player (maximin) game values;
- `μ.restrict I` — the induced payoff function on the points `↥I` of a subinterval;
- `μ.dual` — the order-dual payoff function, exchanging the two players;
- `μ.IsConvex`, `μ.IsSlopeLike`, `μ.IsSemistable`, … — typeclass hypotheses on `μ`;
- `μ.breakpoints I` — the canonical cut points from which filtrations are built;
- `μ.hnFiltration` — the canonical Harder–Narasimhan filtration of `μ`.

Under suitable chain conditions the game values collapse (`μ.A ⊤ = μ.min ⊤`,
`μ.B ⊤ = μ.max ⊤`), the game has a Nash equilibrium exactly when `μ` is semistable, and
iterating the greatest-breakpoint construction produces the (unique, over a linear
codomain) Harder–Narasimhan filtration.  Specializing `ℒ` to the submodule lattice and `μ`
to the finset of associated primes of a subquotient identifies Harder–Narasimhan
filtrations with coprimary filtrations.

## Library structure

Importing `HarderNarasimhan` (the umbrella module [HarderNarasimhan.lean](HarderNarasimhan.lean))
brings in the whole library.  It is organized as one infrastructure file and four blocks:

### Infrastructure

- [HarderNarasimhan/StrictIntvl.lean](HarderNarasimhan/StrictIntvl.lean) — the type
  `StrictIntvl ℒ` of strict intervals `left < right`, its inclusion order and top element,
  and the points type `↥I` with its inherited `BoundedOrder`/`Lattice`/`IsModularLattice`/
  `WellFoundedGT` instances.

### `PayoffFunction/` — the game and its values

- [Defs.lean](HarderNarasimhan/PayoffFunction/Defs.lean) — the `PayoffFunction` structure,
  the operations `max`/`min`/`A`/`B` and their basic API, `IsAttained`, and the order dual.
- [Restrict.lean](HarderNarasimhan/PayoffFunction/Restrict.lean) — restriction to a
  subinterval and its commutation with `max`/`min`/`A`/`B`.
- [Convex.lean](HarderNarasimhan/PayoffFunction/Convex.lean) — the convexity classes
  `IsConvex`/`IsConvexOn`/`IsAffine` and the fundamental inequalities for `μ.A`.
- [Semistable/Defs.lean](HarderNarasimhan/PayoffFunction/Semistable/Defs.lean) —
  `IsSemistable`/`IsStable`, the chain condition `ADCC`, and breakpoints.
- [Semistable/Breakpoints.lean](HarderNarasimhan/PayoffFunction/Semistable/Breakpoints.lean) —
  existence, uniqueness, totality, and the decomposition formula for breakpoints.
- [SlopeLike.lean](HarderNarasimhan/PayoffFunction/SlopeLike.lean) — the slope-like axiom
  and its seesaw trichotomy (`seesaw_*` iff family).
- [Slope.lean](HarderNarasimhan/PayoffFunction/Slope.lean) — the prototypical slope-like
  payoff `slope r d` (degree over rank, valued in a Dedekind–MacNeille completion).
- [GameValue.lean](HarderNarasimhan/PayoffFunction/GameValue.lean) — chain conditions
  (`WeakACC`, `StrongDCC`), computation of the global game values, first-mover advantage.
- [NashEquilibrium.lean](HarderNarasimhan/PayoffFunction/NashEquilibrium.lean) —
  `HasNashEquilibrium` and its equivalence with semistability.

### `Filtration/` — Harder–Narasimhan filtrations

- [Defs.lean](HarderNarasimhan/Filtration/Defs.lean) — the `HarderNarasimhanFiltration`
  structure (explicit `length`, semistable steps, strictly decreasing `μ.A`-slopes) and the
  `Admissible` side condition.
- [Exists.lean](HarderNarasimhan/Filtration/Exists.lean) — the canonical construction
  `μ.hnFiltration` by iterated greatest breakpoints.
- [Unique.lean](HarderNarasimhan/Filtration/Unique.lean) — uniqueness over a complete
  linear order, and the `RelSeries` repackaging.

### `JordanHolder/` — Jordan–Hölder filtrations

- [Defs.lean](HarderNarasimhan/JordanHolder/Defs.lean) — the `JordanHolderFiltration`
  structure (descending chains with total step payoff) and the chain condition
  `EventuallyTopDCC`.
- [Exists.lean](HarderNarasimhan/JordanHolder/Exists.lean) — existence by a greedy minimal
  refinement (a `Nonempty` instance; such filtrations are not unique).
- [Stability.lean](HarderNarasimhan/JordanHolder/Stability.lean) — the step condition is
  equivalent to piecewise stability of the restricted payoffs.
- [Length.lean](HarderNarasimhan/JordanHolder/Length.lean) — over a modular lattice all
  Jordan–Hölder filtrations have the same length.

### `Coprimary/` — coprimary filtrations of modules

- [AssociatedPrimes.lean](HarderNarasimhan/Coprimary/AssociatedPrimes.lean) — pure
  commutative algebra: associated primes of the quotient by a localization kernel
  (Bourbaki, *Algèbre commutative*, Ch. IV, §1, no. 2, Prop. 6).
- [Defs.lean](HarderNarasimhan/Coprimary/Defs.lean) — the coprimary payoff function
  `Coprimary.payoff R M` on the submodule lattice, `IsCoprimary`, and the
  `CoprimaryFiltration` structure.
- [Semistability.lean](HarderNarasimhan/Coprimary/Semistability.lean) — explicit
  computation of the first-player value; semistability is having a unique associated prime.
- [Filtration.lean](HarderNarasimhan/Coprimary/Filtration.lean) — existence and uniqueness
  of the coprimary filtration, via the general Harder–Narasimhan machinery.

[DependencyExtractor.lean](DependencyExtractor.lean) is a development tool that regenerates
the dependency graph [HarderNarasimhan.json](HarderNarasimhan.json) (linked in the badge
above).

## How to read this repository

1. Start with [StrictIntvl.lean](HarderNarasimhan/StrictIntvl.lean) and
   [PayoffFunction/Defs.lean](HarderNarasimhan/PayoffFunction/Defs.lean) for the two core
   types and the game values.
2. Read [Convex.lean](HarderNarasimhan/PayoffFunction/Convex.lean) and the two
   `Semistable/` files for the breakpoint machinery — the heart of the theory.
3. [Filtration/Exists.lean](HarderNarasimhan/Filtration/Exists.lean) and
   [Filtration/Unique.lean](HarderNarasimhan/Filtration/Unique.lean) assemble the main
   theorem on Harder–Narasimhan filtrations.
4. The game-theoretic side ([GameValue.lean](HarderNarasimhan/PayoffFunction/GameValue.lean),
   [NashEquilibrium.lean](HarderNarasimhan/PayoffFunction/NashEquilibrium.lean)) and the
   `JordanHolder/` block can be read independently after step 2.
5. `Coprimary/` shows the abstract theory at work on an honest example from commutative
   algebra.

Each file carries a module docstring (`/-! # … -/`) with its main definitions and results
and closes with a `## References` section pointing to [ChenJeannin].

## Main results at a glance

Declarations live in the namespace `HarderNarasimhan.PayoffFunction` unless qualified
otherwise.  Results that are naturally packaged as conjunctions or `TFAE` blocks are split
into the listed single-conclusion lemmas.

| Result | Lean declaration(s) |
|---|---|
| Fundamental inequality chain for convex payoff functions | `A_le_max_inf`, `IsConvexOn.max_inf_le_max`, `IsConvexOn.A_le_A_sup` |
| Stability of the extremal operations under convexity | `IsConvexOn.max`, `IsConvexOn.max_max`, `IsConvexOn.A_max` |
| Comparison of the first-player value along a chain | `A_anti_left`, `IsConvexOn.inf_le_A`, `IsConvexOn.A_eq_of_ge`, `IsConvexOn.A_le_A_of_lt`, `IsConvexOn.A_eq_or_lt` |
| Complementary segment value after a strict improvement | `IsConvex.A_right_eq_of_A_left_gt` |
| Comparison of the first-player value along a join | `IsConvexOn.inf_A_le_A_sup`, `IsConvexOn.A_le_A_sup_or` |
| Interval enlargement when the first-player value is `⊤` | `IsConvexOn.A_le_of_A_eq_top` |
| Sufficient condition for the descending chain condition | `adcc_of_exists_A_eq_top` |
| Existence of breakpoints | `breakpoints_nonempty` |
| Uniqueness of the breakpoint over a complete linear order | `IsBreakpoint.eq` |
| Semistability below and obstruction above a breakpoint | `IsBreakpoint.isSemistable_restrict`, `IsBreakpoint.not_A_le` |
| Totality, greatest element, and decomposition for breakpoints | `breakpoints_total`, `exists_isGreatest_breakpoints`, `IsBreakpoint.A_eq_A_of_lt` |
| Existence and uniqueness of the Harder–Narasimhan filtration | `hnFiltration`, `Unique (μ.HarderNarasimhanFiltration)`, `exists_relSeries_semistableRel`, `existsUnique_relSeries_semistableRel` |
| Chain equalities of the first-player value along the canonical filtration | `hnFiltration_A_bot_eq_A` |
| Convexity of the coprimary payoff function | the `IsConvexOn ⊤` instance for `Coprimary.payoff R M` |
| First-player value of the coprimary payoff function | `Coprimary.A_payoff` |
| Descending chain condition for the coprimary payoff function | the `ADCC` instance for `Coprimary.payoff R M` |
| Semistable means coprimary | `Coprimary.isSemistable_iff_A_const`, `Coprimary.isSemistable_iff_existsUnique_associatedPrime` |
| Existence and uniqueness of the coprimary filtration | `Coprimary.coprimaryFiltration`, `Unique (CoprimaryFiltration R M)` |
| The associated primes of `M` via the coprimary filtration | `CoprimaryFiltration.associatedPrimes_eq_iUnion` |
| Player A's value collapses to the global minimum | `A_top_eq_min_top`, `A_top_le_B_top` |
| Player B's value collapses to the global maximum | `B_top_eq_max_top`, `A_top_le_B_top_of_strongDCC` |
| Strong descending chain condition from a well-ordered rank | `strongDCC_of_wellOrderedRank` |
| The slope-like axiom as the seesaw trichotomy | `isSlopeLike_iff_seesaw`, `IsSlopeLike.seesaw` |
| The slope of a degree by a rank is slope-like | `isSlopeLike_slope` |
| Unfolded reformulations of the equilibrium condition | `min_le_apply`, `apply_le_max`, `B_top_le_A_top_iff`, `hasNashEquilibrium_iff_min_le`, `hasNashEquilibrium_iff_le_max` |
| Equilibrium inequality vs. coincidence of the extremal values | `B_top_le_A_top_of_min_eq_max`, `min_top_eq_max_top_of_B_top_le_A_top` |
| Equivalence of the endpoint equalities for slope-like payoffs | `max_top_eq_apply_iff`, `min_top_eq_apply_iff` |
| Semistability implies Nash equilibrium | `IsSemistable.B_top_le_A_top`, `IsSemistable.hasNashEquilibrium` |
| Nash equilibrium implies semistability | `isSemistable_of_hasNashEquilibrium` |
| Nash equilibrium iff the global extremal values coincide | `min_top_eq_max_top_iff_hasNashEquilibrium`, `nashEquilibrium_tfae` |
| Existence of Jordan–Hölder filtrations | `Nonempty (μ.JordanHolderFiltration)`, `exists_relSeries_jordanHolderRel` |

Further results include the uniqueness of the Jordan–Hölder length over a modular lattice
(`JordanHolderFiltration.length_eq`), the piecewise-stability characterization
(`piecewise_isStable_iff`), and the commutative algebra input
`HarderNarasimhan.associatedPrimes_quot_ker_mkLinearMap`.

## Building

The repository pins Lean and mathlib via [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml):

```bash
lake exe cache get   # fetch the mathlib build cache
lake build
```

## License

Licensed under the Apache License, Version 2.0.  See [LICENSE](LICENSE).
