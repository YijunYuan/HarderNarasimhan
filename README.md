# HarderNarasimhan

![CI](https://github.com/YijunYuan/HarderNarasimhan/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.27.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-v4.27.0-5C2D91)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 project around the **Harder–Narasimhan game** development.

The repository is structured as a collection of modules defining order-theoretic infrastructure
(intervals, Dedekind–MacNeille completion, lexicographic orders on finsets) and building up
notions such as convexity, slope-like behavior, semistability, and filtrations.

## Mathematical Overview

At a high level, the development is organized around a bounded poset / lattice `ℒ` and an
interval-indexed invariant

- `μ : {p : ℒ × ℒ // p.1 < p.2} → S`,

where `S` is typically a complete lattice (so that we can take `sSup`/`sInf`). One should think of `μ(a,b)`
as measuring the strict interval `(a,b)`.

The core constructions (defined in [HarderNarasimhan/Basic.lean](HarderNarasimhan/Basic.lean)) build
new invariants from `μ` by taking suprema/infima over interior points of an interval, e.g.

- `μmax μ (a,b)`: an extremal value obtained by varying the right endpoint while keeping the left endpoint,
- `μmin μ (a,b)`: the dual extremal construction,
- `μA μ (a,b)` / `μB μ (a,b)`: “outer optimizations” obtained by iterating `μmax`/`μmin`.

From there, the project develops structural hypotheses (convexity, slope-like “seesaw” properties) and
their consequences for semistability and the existence/uniqueness of canonical breakpoints, ultimately
supporting filtration-style statements.

## Project Structure

The library follows a consistent internal pattern: most conceptual modules are split into

- `Defs.lean`: definitions and typeclass interfaces,
- `Impl.lean`: implementation lemmas meant for internal reuse,
- `Results.lean`: user-facing theorems and re-exports.

### Core Infrastructure

- [HarderNarasimhan.lean](HarderNarasimhan.lean): main entry point that re-exports the library.
- [HarderNarasimhan/Basic.lean](HarderNarasimhan/Basic.lean): strict-interval language and the extremal
	constructions (`μmax`, `μmin`, `μA`, `μB`).
- [HarderNarasimhan/Interval.lean](HarderNarasimhan/Interval.lean): the interval subtype `Interval z` and
	the restriction adapter `Resμ`, allowing one to view a global `μ` as an interval-local invariant.

### Main Mathematical Modules

- `Convexity/`: convexity assumptions for `μ` (globally or localized to an interval), and consequences for
	the extremal invariants (`μmax`, `μA`, …).
- `SlopeLike/`: a slope-like axiom for `μ` and an equivalent “seesaw” characterization; includes a quotient
	construction `μQuotient` using the Dedekind–MacNeille completion.
- `Semistability/`: (semi)stability notions formulated in terms of `μA`, selection predicates for canonical
	breakpoints, and existence/uniqueness results under well-foundedness/DCC-style hypotheses.

### Filtrations and Game-Theoretic Layers

- `Filtration/`, `JordanHolderFiltration/`, `CoprimaryFiltration/`: filtration-style constructions and
	results built on top of the semistability layer.
- `NashEquilibrium/`, `FirstMoverAdvantage/`: game-theoretic results and interfaces that connect back to the
	Harder–Narasimhan perspective.

### General Order Theory Utilities

- `OrderTheory/`: auxiliary order-theoretic tools used by multiple modules (e.g. Dedekind–MacNeille
	completion, lexicographic orders on finsets).

## How to Read This Repository

A common entry path is:

1. [HarderNarasimhan/Basic.lean](HarderNarasimhan/Basic.lean) and
   [HarderNarasimhan/Interval.lean](HarderNarasimhan/Interval.lean) for the core interval API.
2. `Convexity/Results.lean` for the main convexity-driven inequalities.
3. `SlopeLike/Result.lean` for the seesaw characterization and the quotient-based construction.
4. `Semistability/Results.lean` for the public semistability statements.
5. Filtration modules (`Filtration/`, `JordanHolderFiltration/`, `CoprimaryFiltration/`) for the
   culminating structural results.

## Minimal Build Notes

This repository pins Lean and mathlib via [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml). If you want to check everything compiles:

```bash
lake update
lake build
```

## Notes

- [HarderNarasimhan/CoprimaryFiltration/CommutativeAlgebra.lean](HarderNarasimhan/CoprimaryFiltration/CommutativeAlgebra.lean)
	collects commutative algebra lemmas used by the coprimary filtration development.
- The codebase aims to keep documentation and style consistent (including line-length checks).

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).