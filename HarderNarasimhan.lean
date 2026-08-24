/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.StrictIntvl

import HarderNarasimhan.PayoffFunction.Defs
import HarderNarasimhan.PayoffFunction.Restrict
import HarderNarasimhan.PayoffFunction.Convex
import HarderNarasimhan.PayoffFunction.Semistable.Defs
import HarderNarasimhan.PayoffFunction.Semistable.Breakpoints
import HarderNarasimhan.PayoffFunction.SlopeLike
import HarderNarasimhan.PayoffFunction.Slope
import HarderNarasimhan.PayoffFunction.GameValue
import HarderNarasimhan.PayoffFunction.NashEquilibrium

import HarderNarasimhan.Filtration.Defs
import HarderNarasimhan.Filtration.Exists
import HarderNarasimhan.Filtration.Unique

import HarderNarasimhan.JordanHolder.Defs
import HarderNarasimhan.JordanHolder.Exists
import HarderNarasimhan.JordanHolder.Stability
import HarderNarasimhan.JordanHolder.Length

import HarderNarasimhan.Coprimary.AssociatedPrimes
import HarderNarasimhan.Coprimary.Defs
import HarderNarasimhan.Coprimary.Semistability
import HarderNarasimhan.Coprimary.Filtration

/-!
# `HarderNarasimhan`: library root

This module is the umbrella import for the project: importing `HarderNarasimhan` brings the
whole formalization of the Harder–Narasimhan game of [ChenJeannin] into scope.  It declares no
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
