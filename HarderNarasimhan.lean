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
# Harder–Narasimhan games

A Harder–Narasimhan game is a two-player game on a bounded lattice. Player A chooses a left
endpoint `a` and minimizes the payoff; player B chooses a right endpoint `b` and maximizes it,
subject to `a < b`. A payoff function assigns a value in a complete lattice to each such pair.

This library develops the game values, semistability, and filtrations of these games, following
[ChenJeannin]. For convex admissible payoffs satisfying suitable chain conditions,
Harder–Narasimhan filtrations exist and are unique when the payoff order is linear.
For slope-like payoffs, semistability is related to Nash equilibrium and to the existence of
Jordan–Hölder filtrations. Applied to associated primes of subquotients, the construction gives
coprimary filtrations of nonzero finitely generated modules over Noetherian commutative rings.

## Main definitions

* `HarderNarasimhan.StrictIntvl`: pairs of endpoints `a < b`.
* `HarderNarasimhan.PayoffFunction`: payoff functions on strict intervals.
* `HarderNarasimhan.PayoffFunction.HarderNarasimhanFiltration`: filtrations with semistable
  steps whose successive game values $s_i$ satisfy $s_i \not\le s_{i+1}$.
* `HarderNarasimhan.PayoffFunction.JordanHolderFiltration`: filtrations with stable steps
  having the same payoff as the whole lattice.
* `HarderNarasimhan.CoprimaryFiltration`: filtrations with coprimary subquotients and
  decreasing associated primes in a fixed linear extension of the prime spectrum.

This module imports the whole library. The individual files in `HarderNarasimhan/PayoffFunction/`,
`HarderNarasimhan/Filtration/`, `HarderNarasimhan/JordanHolder/`, and `HarderNarasimhan/Coprimary/`
can also be imported separately.

## References

* [Huayi Chen and Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/
