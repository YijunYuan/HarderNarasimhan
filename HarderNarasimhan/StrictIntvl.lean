/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Sublattice
import Mathlib.Order.ModularLattice

/-!
# Strict intervals

This file defines `StrictIntvl ℒ`, the type of *strict intervals* in an order `ℒ`: ordered
pairs of endpoints `left < right`.  Strict intervals index every payoff function in this
library; strictness is part of the data, so no use site ever needs to carry a nondegeneracy
side condition.

`StrictIntvl ℒ` is partially ordered by inclusion, and when `ℒ` is a nontrivial bounded
order the total interval `(⊥, ⊤)` is its top element `⊤`.

A strict interval `I` is also viewed as a self-contained bounded order through its coercion
to sort: `↥I` is the subtype of points lying between the endpoints, with `⊥ = I.left` and
`⊤ = I.right`.  Lattice structure, modularity and well-foundedness of `>` all descend from
`ℒ` to `↥I`.

## Main definitions

* `StrictIntvl ℒ`: the type of strict intervals `left < right` in `ℒ`, with membership
  `x ∈ I ↔ I.left ≤ x ∧ x ≤ I.right` and the inclusion order.
* The points type `↥I`, together with its inherited `BoundedOrder`, `Lattice`,
  `IsModularLattice` and `WellFoundedGT` instances.
* `StrictIntvl.ofSub`: reinterpret a strict interval of `↥I` as a strict interval of `ℒ`;
  the preferred spelling is the coercion `↑J`.
-/

namespace HarderNarasimhan

/-- A *strict interval* in `ℒ`: an ordered pair of endpoints `left < right`. -/
@[ext]
structure StrictIntvl (ℒ : Type*) [LT ℒ] where
  /-- The left endpoint. -/
  left : ℒ
  /-- The right endpoint. -/
  right : ℒ
  /-- The endpoints are in strict order. -/
  lt : left < right

namespace StrictIntvl

variable {ℒ : Type*}

section Membership

variable [LT ℒ] [LE ℒ]

/-- Membership in a strict interval: `x ∈ I` means `I.left ≤ x ∧ x ≤ I.right`. -/
instance : Membership ℒ (StrictIntvl ℒ) :=
  ⟨fun I x ↦ I.left ≤ x ∧ x ≤ I.right⟩

lemma mem_def {I : StrictIntvl ℒ} {x : ℒ} : x ∈ I ↔ I.left ≤ x ∧ x ≤ I.right := Iff.rfl

end Membership

section Preorder

variable [Preorder ℒ]

/-- Membership in a strict interval agrees with membership in the closed interval
`Set.Icc I.left I.right`. -/
lemma mem_iff_mem_Icc {I : StrictIntvl ℒ} {x : ℒ} : x ∈ I ↔ x ∈ Set.Icc I.left I.right :=
  Iff.rfl

@[simp] lemma left_mem (I : StrictIntvl ℒ) : I.left ∈ I := ⟨le_rfl, I.lt.le⟩

@[simp] lemma right_mem (I : StrictIntvl ℒ) : I.right ∈ I := ⟨I.lt.le, le_rfl⟩

end Preorder

section PartialOrder

variable [PartialOrder ℒ]

/-- Strict intervals are partially ordered by inclusion: `I ≤ J` means that `I` is a
subinterval of `J`, i.e. `J.left ≤ I.left ∧ I.right ≤ J.right`. -/
instance : PartialOrder (StrictIntvl ℒ) where
  le I J := J.left ≤ I.left ∧ I.right ≤ J.right
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hIJ hJK := ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩
  le_antisymm _ _ hIJ hJI := StrictIntvl.ext (le_antisymm hJI.1 hIJ.1) (le_antisymm hIJ.2 hJI.2)

lemma le_def {I J : StrictIntvl ℒ} : I ≤ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right := Iff.rfl

end PartialOrder

section OrderTop

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]

/-- When `ℒ` is a nontrivial bounded order, the total interval `(⊥, ⊤)` is the greatest
strict interval with respect to inclusion. -/
instance : OrderTop (StrictIntvl ℒ) where
  top := ⟨⊥, ⊤, bot_lt_top⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp] lemma left_top : (⊤ : StrictIntvl ℒ).left = ⊥ := rfl

@[simp] lemma right_top : (⊤ : StrictIntvl ℒ).right = ⊤ := rfl

/-- Every element lies in the total interval `⊤`. -/
@[simp] lemma mem_top (x : ℒ) : x ∈ (⊤ : StrictIntvl ℒ) := ⟨bot_le, le_top⟩

/-- An interval with endpoints `⊥` and `⊤` is the total interval `⊤`, whatever the proof. -/
@[simp] lemma mk_bot_top (h : (⊥ : ℒ) < ⊤) : (⟨⊥, ⊤, h⟩ : StrictIntvl ℒ) = ⊤ := rfl

end OrderTop

/-! ### The points of a strict interval

The coercion to sort realises a strict interval `I` as the subtype `{x // x ∈ I}` of its
points, a self-contained bounded order with `⊥ = I.left` and `⊤ = I.right`. -/

/-- The type of points of a strict interval: `↥I` is the subtype `{x // x ∈ I}`. -/
instance [LT ℒ] [LE ℒ] : CoeSort (StrictIntvl ℒ) (Type _) :=
  ⟨fun I ↦ {x // x ∈ I}⟩

section Points

variable [PartialOrder ℒ] {I : StrictIntvl ℒ}

/-- `↥I` is nontrivial: the two endpoints are distinct points of `I`. -/
instance : Nontrivial ↥I :=
  ⟨⟨I.left, I.left_mem⟩, ⟨I.right, I.right_mem⟩, by simpa [Subtype.ext_iff] using I.lt.ne⟩

/-- `↥I` is a bounded order: `⊥` is the left endpoint and `⊤` is the right endpoint. -/
instance : BoundedOrder ↥I where
  bot := ⟨I.left, I.left_mem⟩
  bot_le a := a.prop.1
  top := ⟨I.right, I.right_mem⟩
  le_top a := a.prop.2

@[simp] lemma val_bot : (⊥ : ↥I).val = I.left := rfl

@[simp] lemma val_top : (⊤ : ↥I).val = I.right := rfl

/-- Well-foundedness of `>` is inherited by intervals: the strict order on `↥I` is the
pullback of the strict order on `ℒ` along `Subtype.val`, so well-foundedness transports
along `InvImage.wf`. -/
instance [hw : WellFoundedGT ℒ] : WellFoundedGT ↥I :=
  ⟨Subrelation.wf (fun h ↦ Subtype.coe_lt_coe.mpr h) (InvImage.wf Subtype.val hw.wf)⟩

/-- Reinterpret a strict interval of `↥I` as a strict interval of the ambient order `ℒ`.

This is the canonical adapter between the relative and the ambient viewpoints; the
preferred spelling is the coercion arrow `↑J` provided by the `CoeOut` instance below. -/
def ofSub (J : StrictIntvl ↥I) : StrictIntvl ℒ :=
  ⟨J.left, J.right, Subtype.coe_lt_coe.2 J.lt⟩

instance : CoeOut (StrictIntvl ↥I) (StrictIntvl ℒ) := ⟨ofSub⟩

@[simp] lemma ofSub_left (J : StrictIntvl ↥I) : (ofSub J).left = J.left.val := rfl

@[simp] lemma ofSub_right (J : StrictIntvl ↥I) : (ofSub J).right = J.right.val := rfl

/-- The total interval of `↥I` maps back to `I` itself under `ofSub`. -/
@[simp] lemma ofSub_top : ofSub (⊤ : StrictIntvl ↥I) = I := rfl

end Points

section Lattice

variable [Lattice ℒ] {I : StrictIntvl ℒ}

/-- If `ℒ` is a lattice, then `↥I` is a lattice with `⊔`/`⊓` computed in `ℒ`: the interval
is closed under `⊔` and `⊓` by the endpoint bounds stored in the membership proofs. -/
instance : Lattice ↥I :=
  Subtype.lattice (fun _ _ hx hy ↦ ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩)
    (fun _ _ hx hy ↦ ⟨le_inf hx.1 hy.1, le_trans inf_le_right hy.2⟩)

/-- Intervals in a modular lattice are modular. -/
instance [iml : IsModularLattice ℒ] : IsModularLattice ↥I where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    exact iml.sup_inf_le_assoc_of_le y.val hxz

end Lattice

end StrictIntvl

end HarderNarasimhan
