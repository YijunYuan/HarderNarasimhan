/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.SlopeLike.Impl

/-!
# Section 4.3: slope-like payoff functions — statements

The numbered results of Section 4.3; proofs are in `SlopeLike.Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ] [CompleteLattice S]

/-- Proposition 4.6. Slope-likeness is equivalent to the seesaw trichotomy. -/
theorem proposition_4_6 (μ : PayoffFunction ℒ S) :
    μ.IsSlopeLike ↔ ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
      (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
      (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) :=
  Impl.PayoffFunction.isSlopeLike_iff_seesaw

/-- Proposition 4.8. An additive degree divided by an additive nonnegative rank is slope-like when
degree is positive at rank zero. Definition 4.7 is expressed by the ordered-space instances;
the implementation assumes the ordered vector space is nontrivial. -/
theorem proposition_4_8 {V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V]
    [IsOrderedAddMonoid V] [PosSMulStrictMono ℝ V] [Nontrivial V]
    (r : StrictIntvl ℒ → NNReal) (d : StrictIntvl ℒ → V)
    (hadd : ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      d ⟨x, z, h₁.trans h₂⟩ = d ⟨x, y, h₁⟩ + d ⟨y, z, h₂⟩ ∧
      r ⟨x, z, h₁.trans h₂⟩ = r ⟨x, y, h₁⟩ + r ⟨y, z, h₂⟩)
    (hpos : ∀ (x y : ℒ), (h : x < y) → r ⟨x, y, h⟩ = 0 → 0 < d ⟨x, y, h⟩) :
    (slope r d).IsSlopeLike :=
  Impl.PayoffFunction.isSlopeLike_slope r d (fun x y z h₁ h₂ ↦ (hadd x y z h₁ h₂).1)
    (fun x y z h₁ h₂ ↦ (hadd x y z h₁ h₂).2) hpos

end HarderNarasimhan
