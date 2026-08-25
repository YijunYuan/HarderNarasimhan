/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.StrictIntvl

public import HarderNarasimhan.PayoffFunction.Convex
public import HarderNarasimhan.PayoffFunction.Defs
public import HarderNarasimhan.PayoffFunction.GameValue
public import HarderNarasimhan.PayoffFunction.NashEquilibrium
public import HarderNarasimhan.PayoffFunction.Restrict
public import HarderNarasimhan.PayoffFunction.Semistable.Breakpoints
public import HarderNarasimhan.PayoffFunction.Semistable.Defs
public import HarderNarasimhan.PayoffFunction.Slope
public import HarderNarasimhan.PayoffFunction.SlopeLike

public import HarderNarasimhan.Filtration.Defs
public import HarderNarasimhan.Filtration.Exists
public import HarderNarasimhan.Filtration.Unique

public import HarderNarasimhan.JordanHolder.Defs
public import HarderNarasimhan.JordanHolder.Exists
public import HarderNarasimhan.JordanHolder.Length
public import HarderNarasimhan.JordanHolder.Stability

public import HarderNarasimhan.Coprimary.AssociatedPrimes
public import HarderNarasimhan.Coprimary.Defs
public import HarderNarasimhan.Coprimary.Filtration
public import HarderNarasimhan.Coprimary.Semistability

/-!
# `HarderNarasimhan`: library root

This module is the umbrella import for the project: importing `HarderNarasimhan` brings the
whole formalization of the Harder–Narasimhan Games of [ChenJeannin] into scope.  It declares no
definitions or lemmas of its own.

The library is organized in four blocks on top of the interval infrastructure
`HarderNarasimhan.StrictIntvl`:

* `HarderNarasimhan.PayoffFunction.*` : the bundled `PayoffFunction` structure, the game values
  `μ.max`/`μ.min`/`μ.A`/`μ.B`, restriction to subintervals, convexity, slope-like payoffs,
  semistability and breakpoints, first-mover advantage, and Nash equilibria.
* `HarderNarasimhan.Filtration.*` : Harder–Narasimhan filtrations — existence (`μ.hnFiltration`)
  and uniqueness over a complete linear order.
* `HarderNarasimhan.JordanHolder.*` : Jordan–Hölder filtrations — existence, piecewise stability,
  and uniqueness of the length over a modular lattice.
* `HarderNarasimhan.Coprimary.*` : the coprimary filtration of a finitely generated module over a
  Noetherian ring, as an instance of the abstract theory.

For finer-grained dependencies, import the individual files instead.
-/
