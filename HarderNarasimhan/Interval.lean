/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic

/-!
This file provides `Resμ`, the restriction of an interval-indexed function `μ` on `ℒ` to an
interval measure on the points `↥I` of a strict interval `I`, together with the lemmas stating
that the induced constructions (`μmax`, `μmin`, `μA`, `μB`) commute with restriction.

NOTE (refactor in progress): this transitional file will be replaced by
`HarderNarasimhan.PayoffFunction.Restrict`, where `Resμ` becomes `PayoffFunction.restrict`.
-/

namespace HarderNarasimhan

/--
`Resμ I μ` restricts an interval-indexed function `μ` on `ℒ` to the interval `↥I`.

Concretely, a strict interval `J` of `↥I` is sent to `μ ↑J`. This is the core adapter used
throughout the development to reuse global constructions on subintervals.
-/
def Resμ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(I : StrictIntvl ℒ) {S : Type*} [CompleteLattice S] (μ : PayoffFunction ℒ S) :
PayoffFunction ↥I S := ⟨fun J ↦ μ ↑J⟩

/--
Unfolding lemma for restriction: evaluating `Resμ` is definitionally `μ` on the underlying strict
interval.
-/
lemma μ_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : StrictIntvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S}
{J : StrictIntvl ↥I} :
(Resμ I μ) J = μ ↑J := rfl

/--
Restriction commutes with the “left-anchored supremum” construction `μmax`.
-/
lemma μmax_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : StrictIntvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S}
{J : StrictIntvl ↥I} :
μmax (Resμ I μ) J = μmax μ ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le
      ⟨a, le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)

/--
Restriction commutes with the “right-anchored infimum” construction `μmin`.
This is the dual statement to `μmax_res_intvl`.
-/
lemma μmin_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : StrictIntvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S}
{J : StrictIntvl ↥I} :
μmin (Resμ I μ) J = μmin μ ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩ le_rfl)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩ le_rfl)

/--
Restriction commutes with `μA`, the infimum over right-endpoints of `μmax` values.

This lemma is a key “locality” principle: computations of `μA` can be performed on subintervals.
-/
lemma μA_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : StrictIntvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S}
{J : StrictIntvl ↥I} :
μA (Resμ I μ) J = μA μ ↑J :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le
      ⟨a, le_trans J.left.prop.1 ha.1, le_trans ha.2.le J.right.prop.2⟩ ⟨ha.1, ha.2⟩
      μmax_res_intvl.le)
    (le_iInf₂ fun u hu ↦ iInf₂_le_of_le u.val ⟨hu.1, hu.2⟩
      (μmax_res_intvl (J := ⟨u, J.right, hu.2⟩)).ge)

/--
Restriction commutes with `μB`, the supremum over left-endpoints of `μmin` values.

This is the `μB`-analogue of `μA_res_intvl`.
-/
lemma μB_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : StrictIntvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S}
{J : StrictIntvl ↥I} :
μB (Resμ I μ) J = μB μ ↑J :=
  le_antisymm
    (iSup₂_le fun u hu ↦ le_iSup₂_of_le u.val ⟨hu.1, hu.2⟩ μmin_res_intvl.le)
    (iSup₂_le fun a ha ↦
      have hmem : a ∈ I := ⟨le_trans J.left.prop.1 ha.1.le, le_trans ha.2 J.right.prop.2⟩
      le_iSup₂_of_le ⟨a, hmem⟩ ⟨ha.1, ha.2⟩
        (μmin_res_intvl (J := ⟨J.left, ⟨a, hmem⟩, ha.1⟩)).ge)

end HarderNarasimhan
