/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Defs

/-!
# Restriction of payoff functions

A payoff function on `ℒ` restricts to the closed interval of points `↥I` of a strict interval
`I`. The four operations `max`, `min`, `A` and `B` commute with restriction, so their values
on a subinterval agree whether computed in `ℒ` or in `↥I`.

## Main definitions

* `HarderNarasimhan.PayoffFunction.restrict`: restriction to the points of an interval.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ]

/-- Definition 2.2, the restricted game. The restriction of `μ` to the points of `I`. A strict
interval `J` in `↥I` has payoff
`μ ↑J`, where `↑J` is the corresponding interval in `ℒ`. -/
def restrict (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : PayoffFunction ↥I S :=
  ⟨fun J ↦ μ ↑J⟩

/-- Auxiliary restriction identity for Definition 2.2: restrict apply. -/
@[simp] lemma restrict_apply (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (J : StrictIntvl ↥I) : μ.restrict I J = μ ↑J :=
  rfl

variable [CompleteLattice S] {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Auxiliary restriction identity for Definition 2.2: max restrict apply. -/
lemma max_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).max J = μ.max ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le
      ⟨a, le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)

/-- Auxiliary restriction identity for Definition 2.2. Restriction commutes with `max`. -/
@[simp] lemma max_restrict : (μ.restrict I).max = μ.max.restrict I :=
  ext fun _ ↦ max_restrict_apply

/-- Auxiliary restriction identity for Definition 2.2: min restrict apply. -/
lemma min_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).min J = μ.min ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)

/-- Auxiliary restriction identity for Definition 2.2. Restriction commutes with `min`. -/
@[simp] lemma min_restrict : (μ.restrict I).min = μ.min.restrict I :=
  ext fun _ ↦ min_restrict_apply

/-- Auxiliary restriction identity for Definition 2.2: A restrict apply. -/
lemma A_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).A J = μ.A ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩
      max_restrict_apply.le)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩
      (max_restrict_apply (J := ⟨u, J.right, hu.2⟩)).ge)

/-- Auxiliary restriction identity for Definition 2.2. Restriction commutes with `A`. -/
@[simp] lemma A_restrict : (μ.restrict I).A = μ.A.restrict I :=
  ext fun _ ↦ A_restrict_apply

/-- Auxiliary restriction identity for Definition 2.2: B restrict apply. -/
lemma B_restrict_apply {J : StrictIntvl ↥I} : (μ.restrict I).B J = μ.B ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ min_restrict_apply.le)
    (iSup₂_le fun a ha ↦
      have hmem : a ∈ I := ⟨le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩
      le_iSup₂_of_le ⟨a, hmem⟩ ⟨ha.1, ha.2⟩
        (min_restrict_apply (J := ⟨J.left, ⟨a, hmem⟩, ha.1⟩)).ge)

/-- Auxiliary restriction identity for Definition 2.2. Restriction commutes with `B`. -/
@[simp] lemma B_restrict : (μ.restrict I).B = μ.B.restrict I :=
  ext fun _ ↦ B_restrict_apply

end PayoffFunction

end HarderNarasimhan
