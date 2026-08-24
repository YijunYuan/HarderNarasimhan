/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.PayoffFunction.Defs

/-!
# Restriction of payoff functions

This file defines `μ.restrict I`, the restriction of a payoff function `μ` on `ℒ` to the
points `↥I` of a strict interval `I`, and proves that the four extremal operations commute
with restriction:

* `max_restrict` : `(μ.restrict I).max = μ.max.restrict I`, and the analogous
  `min_restrict`, `A_restrict`, `B_restrict`.

These are key “locality” principles: computations of `μ.max`, `μ.min`, `μ.A` and `μ.B` can
be performed on subintervals.  Pointwise versions (`max_restrict_apply`, …) are provided for
rewriting a single value.
-/

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ]

/-- `μ.restrict I` is the restriction of the payoff function `μ` to the points of `I`: a
strict interval `J` of `↥I` is sent to `μ ↑J`.  This is the core adapter used throughout the
development to reuse global constructions on subintervals. -/
def restrict (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : PayoffFunction ↥I S :=
  ⟨fun J ↦ μ ↑J⟩

@[simp] lemma restrict_apply (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (J : StrictIntvl ↥I) : μ.restrict I J = μ ↑J :=
  rfl

variable [CompleteLattice S] {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

lemma max_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).max J = μ.max ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le
      ⟨a, le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)

/-- Restriction commutes with `max`. -/
@[simp] lemma max_restrict : (μ.restrict I).max = μ.max.restrict I :=
  ext fun _ ↦ max_restrict_apply

lemma min_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).min J = μ.min ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)

/-- Restriction commutes with `min`. -/
@[simp] lemma min_restrict : (μ.restrict I).min = μ.min.restrict I :=
  ext fun _ ↦ min_restrict_apply

lemma A_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).A J = μ.A ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩
      max_restrict_apply.le)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩
      (max_restrict_apply (J := ⟨u, J.right, hu.2⟩)).ge)

/-- Restriction commutes with `A`. -/
@[simp] lemma A_restrict : (μ.restrict I).A = μ.A.restrict I :=
  ext fun _ ↦ A_restrict_apply

lemma B_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).B J = μ.B ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ min_restrict_apply.le)
    (iSup₂_le fun a ha ↦
      have hmem : a ∈ I := ⟨le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩
      le_iSup₂_of_le ⟨a, hmem⟩ ⟨ha.1, ha.2⟩
        (min_restrict_apply (J := ⟨J.left, ⟨a, hmem⟩, ha.1⟩)).ge)

/-- Restriction commutes with `B`. -/
@[simp] lemma B_restrict : (μ.restrict I).B = μ.B.restrict I :=
  ext fun _ ↦ B_restrict_apply

end PayoffFunction

end HarderNarasimhan
