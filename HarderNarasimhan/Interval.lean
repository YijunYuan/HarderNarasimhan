/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Sublattice

import HarderNarasimhan.Basic

/-!
This file equips a strict interval `I : Intvl ℒ` with its type of points `↥I` and provides a
systematic way to restrict an “interval measure” `μ` on `ℒ` to an interval measure on `↥I`.

Given `I : Intvl ℒ`, the coercion-to-sort `↥I` is the subtype `{x // x ∈ I}` of elements between
the endpoints. The file equips `↥I` with the expected algebraic structures (nontriviality, lattice
operations, bounds — the partial order comes from the generic subtype instance), and provides:

- `Intvl.ofSub` : reinterpret a strict interval of `↥I` as a strict interval of `ℒ`;
- `Resμ I μ` : the induced measure on `↥I`, i.e. `fun J ↦ μ J.ofSub`;
- lemmas `μ*_res_intvl` stating that the induced constructions (`μmax`, `μmin`, `μA`, `μB`)
  commute with restriction;
- `Intvl.val_bot`/`Intvl.val_top`, projection lemmas for the endpoints in the
  interval-as-bounded-order
  view.
-/

namespace HarderNarasimhan

namespace Intvl

/--
The type of points of a strict interval: `↥I` is the subtype `{x // x ∈ I}`.

Instances on `↥I` attach to this subtype; the partial order is the generic subtype order.
-/
instance {ℒ : Type*} [LT ℒ] [LE ℒ] : CoeSort (Intvl ℒ) (Type _) :=
  ⟨fun I ↦ {x // x ∈ I}⟩

/--
`↥I` is nontrivial: the two endpoints are distinct points of `I`.
-/
instance {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} : Nontrivial ↥I :=
  ⟨⟨I.left, I.left_mem⟩, ⟨I.right, I.right_mem⟩, by simpa [Subtype.ext_iff] using I.lt.ne⟩

/--
If `ℒ` is a lattice, then `↥I` is a lattice with `⊔`/`⊓` computed in `ℒ`.

Mathematically, the interval is closed under sup/inf; the closure proofs are discharged
using the endpoint bounds stored in the membership proof, and `Subtype.lattice` does the rest.
-/
instance {ℒ : Type*} [Lattice ℒ] {I : Intvl ℒ} : Lattice ↥I :=
  Subtype.lattice (fun _ _ hx hy ↦ ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩)
    (fun _ _ hx hy ↦ ⟨le_inf hx.1 hy.1, le_trans inf_le_right hy.2⟩)

/--
`↥I` inherits a bounded order structure: `⊥` is the left endpoint and `⊤` is the right endpoint.

This turns the interval into a self-contained bounded poset.
-/
instance {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} : BoundedOrder ↥I where
  bot := ⟨I.left, I.left_mem⟩
  bot_le := fun a ↦ a.prop.1
  top := ⟨I.right, I.right_mem⟩
  le_top := fun a ↦ a.prop.2

/--
Well-foundedness is inherited by intervals: if `ℒ` is well-founded with respect to `>` (i.e. no
infinite strictly descending chains), then so is `↥I`.

API note: the strict order on `↥I` is the pullback of the strict order on `ℒ` along
`Subtype.val`, so well-foundedness transports along `InvImage.wf`.
-/
instance {ℒ : Type*} [PartialOrder ℒ] [hw : WellFoundedGT ℒ] {I : Intvl ℒ} : WellFoundedGT ↥I :=
  ⟨Subrelation.wf (fun h ↦ Subtype.coe_lt_coe.mpr h) (InvImage.wf Subtype.val hw.wf)⟩

/--
Reinterpret a strict interval of `↥I` as a strict interval of the ambient order `ℒ`.

This is the canonical adapter between the relative and the ambient viewpoints; it replaces
by-hand endpoint unpacking at every use site.
-/
def ofSub {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} (J : Intvl ↥I) : Intvl ℒ :=
  ⟨J.left, J.right, Subtype.coe_lt_coe.2 J.lt⟩

/--
The coercion arrow `↑J : Intvl ℒ` is the preferred spelling of `Intvl.ofSub J`.
-/
instance {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} : CoeOut (Intvl ↥I) (Intvl ℒ) := ⟨ofSub⟩

@[simp] lemma ofSub_left {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} (J : Intvl ↥I) :
    (ofSub J).left = J.left.val := rfl

@[simp] lemma ofSub_right {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} (J : Intvl ↥I) :
    (ofSub J).right = J.right.val := rfl

/-- The total interval of `↥I` maps back to `I` itself under `ofSub`. -/
@[simp] lemma ofSub_top {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} :
    ofSub (⊤ : Intvl ↥I) = I := rfl

end Intvl

/--
`Resμ I μ` restricts an interval-indexed function `μ` on `ℒ` to the interval `↥I`.

Concretely, a strict interval `J` of `↥I` is sent to `μ ↑J`. This is the core adapter used
throughout the development to reuse global constructions on subintervals.
-/
def Resμ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(I : Intvl ℒ) {S : Type*} [CompleteLattice S] (μ : Intvl ℒ → S) :
Intvl ↥I → S := fun J ↦ μ ↑J

/--
Common index-set bijection behind the `_res_intvl` lemmas below: interior points of a strict
interval `J` inside `↥I` (cut out by a side condition `D`) correspond to interior points of
`↑J` in `ℒ` (cut out by the corresponding ambient condition `C`).

The value function `f` may depend on the ambient membership proof; all proof positions are
handled by proof irrelevance.
-/
private lemma res_intvl_set_eq {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ} {S : Type*} [CompleteLattice S]
{J : Intvl ↥I}
{D : ↥I → Prop} {C : ℒ → Prop}
(hDC : ∀ u : ↥I, u ∈ J → (D u ↔ C u.val))
(f : (a : ℒ) → a ∈ (↑J : Intvl ℒ) ∧ C a → S) :
{x | ∃ (u : ↥I) (h : u ∈ J ∧ D u), f u.val ⟨⟨h.1.1, h.1.2⟩, (hDC u h.1).1 h.2⟩ = x} =
{x | ∃ (a : ℒ) (h : a ∈ (↑J : Intvl ℒ) ∧ C a), f a h = x} := by
  ext x
  constructor
  · rintro ⟨u, h, rfl⟩
    exact ⟨u.val, ⟨⟨h.1.1, h.1.2⟩, (hDC u h.1).1 h.2⟩, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨a, le_trans J.left.prop.1 h.1.1, le_trans h.1.2 J.right.prop.2⟩,
      ⟨⟨h.1.1, h.1.2⟩, (hDC _ ⟨h.1.1, h.1.2⟩).2 h.2⟩, rfl⟩

/--
Unfolding lemma for restriction: evaluating `Resμ` is definitionally `μ` on the underlying strict
interval.

API note: written as a lemma to make rewriting with `simp`/`rw` explicit downstream.
-/
lemma μ_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
{J : Intvl ↥I} :
------------
(Resμ I μ) J = μ ↑J
------------
:= rfl

/--
Restriction commutes with the “left-anchored supremum” construction `μmax` from `Basic.lean`.

Mathematically, taking `μmax` inside an interval is the same as taking `μmax` in `ℒ` after
forgetting the interval subtype.
-/
lemma μmax_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
{J : Intvl ↥I} :
------------
μmax (Resμ I μ) J = μmax μ ↑J
------------
:= by
  unfold μmax
  simp only [μ_res_intvl, ne_eq]
  exact congrArg sSup <| res_intvl_set_eq (D := fun u ↦ ¬J.left = u)
    (C := fun a ↦ ¬(Intvl.ofSub J).left = a) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μ ⟨(Intvl.ofSub J).left, a, lt_of_le_of_ne h.1.1 h.2⟩

/--
Restriction commutes with the “right-anchored infimum” construction `μmin` from `Basic.lean`.

This is the dual statement to `μmax_res_intvl`.
-/
lemma μmin_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
{J : Intvl ↥I} :
------------
μmin (Resμ I μ) J = μmin μ ↑J
------------
:= by
  unfold μmin
  simp only [μ_res_intvl, ne_eq]
  exact congrArg sInf <| res_intvl_set_eq (D := fun u ↦ ¬u = J.right)
    (C := fun a ↦ ¬a = (Intvl.ofSub J).right) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μ ⟨a, (Intvl.ofSub J).right, lt_of_le_of_ne h.1.2 h.2⟩

/--
Restriction commutes with `μA`, the infimum over right-endpoints of `μmax` values.

This lemma is a key “locality” principle: computations of `μA` can be performed on subintervals.
-/
lemma μA_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
{J : Intvl ↥I} :
------------
μA (Resμ I μ) J = μA μ ↑J
------------
:= by
  unfold μA
  simp only [μmax_res_intvl, ne_eq]
  exact congrArg sInf <| res_intvl_set_eq (D := fun u ↦ ¬u = J.right)
    (C := fun a ↦ ¬a = (Intvl.ofSub J).right) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μmax μ ⟨a, (Intvl.ofSub J).right, lt_of_le_of_ne h.1.2 h.2⟩

/--
Restriction commutes with `μB`, the supremum over left-endpoints of `μmin` values.

This is the `μB`-analogue of `μA_res_intvl`.
-/
lemma μB_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : Intvl ℒ}
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
{J : Intvl ↥I} :
------------
μB (Resμ I μ) J = μB μ ↑J
------------
:= by
  unfold μB
  simp only [μmin_res_intvl, ne_eq]
  exact congrArg sSup <| res_intvl_set_eq (D := fun u ↦ ¬J.left = u)
    (C := fun a ↦ ¬(Intvl.ofSub J).left = a) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μmin μ ⟨(Intvl.ofSub J).left, a, lt_of_le_of_ne h.1.1 h.2⟩

/--
Projection lemma: the bottom element of the points type `↥I` is the left endpoint of `I`.
-/
@[simp] lemma Intvl.val_bot {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} :
    (⊥ : ↥I).val = I.left := rfl

/--
Projection lemma: the top element of the points type `↥I` is the right endpoint of `I`.
-/
@[simp] lemma Intvl.val_top {ℒ : Type*} [PartialOrder ℒ] {I : Intvl ℒ} :
    (⊤ : ↥I).val = I.right := rfl

end HarderNarasimhan
