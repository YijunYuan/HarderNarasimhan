/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Completion

/-!
# Section 4.3: slope-like payoff functions — definitions

Definition 4.5 is `PayoffFunction.IsSlopeLike`. Definition 4.7 is represented by
Mathlib’s ordered real vector-space typeclasses, and `PayoffFunction.slope` is
the quotient construction in Proposition 4.8.
-/

@[expose] public section

open scoped NNReal

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ] [CompleteLattice S]

/-- Definition 4.5. A payoff function is slope-like if, for `x < y < z`, the payoffs on `(x, y)`,
`(x, z)` and `(y, z)` satisfy the seesaw condition.

The four alternatives below are equivalent to these three values being strictly increasing,
strictly decreasing, or all equal; see
`HarderNarasimhan.Impl.PayoffFunction.isSlopeLike_iff_seesaw`. -/
class IsSlopeLike (μ : PayoffFunction ℒ S) : Prop where
  /-- Definition 4.5 (1)–(4): the four-fold seesaw condition. -/
  slopelike : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
    (μ ⟨x, y, h.1⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩) ∧
    (μ ⟨x, y, h.1⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩) ∧
    (μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨y, z, h.2⟩) ∧
    (μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨y, z, h.2⟩)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
  [PosSMulStrictMono ℝ V]

/-- Proposition 4.8 (construction). The slope of a rank `r` and degree `d`, with values in the
Dedekind–MacNeille completion. It is the principal cut of `(r I)⁻¹ • d I` when `r I > 0`, and
`⊤` when `r I = 0`. -/
noncomputable def slope (r : StrictIntvl ℒ → ℝ≥0) (d : StrictIntvl ℒ → V) :
    PayoffFunction ℒ (DedekindCut V) :=
  ⟨fun I ↦ if _ : 0 < r I then .principal ((r I)⁻¹ • d I) else ⊤⟩

end PayoffFunction

end HarderNarasimhan
