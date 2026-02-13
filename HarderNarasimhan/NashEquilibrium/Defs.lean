/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic

/-!
# Nash equilibrium for the Harder–Narasimhan game

This file introduces the `NashEquilibrium` predicate for a slope-like payoff function `μ`.
The game-theoretic quantity `μAstar μ` is the value achievable by player A (via an infimum of
suprema), and `μBstar μ` is the value achievable by player B (via a supremum of infima).

A Nash equilibrium is encoded as the equality `μAstar μ = μBstar μ`.

API overview:

* The primary exported item is the class `NashEquilibrium μ`.
* Most users should import `HarderNarasimhan.NashEquilibrium.Results` for the numbered
  propositions/remarks and their ready-to-use formulations.
-/

namespace HarderNarasimhan

/-
`NashEquilibrium μ` asserts equality of the two game values `μAstar μ` and `μBstar μ`.
Intuitively, this means the minimax and maximin values coincide, so the Harder–Narasimhan
game associated to `μ` has a value.

API note: this is the user-facing predicate capturing “the game has a value”.
-/
class NashEquilibrium {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  nash_eq : μAstar μ = μBstar μ

end HarderNarasimhan
