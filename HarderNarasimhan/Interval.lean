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
This file defines the order-theoretic interval `Interval z` inside a bounded poset/lattice `ℒ`.

Given a strict interval endpoint pair `z : {p : ℒ × ℒ // p.1 < p.2}`, the type `Interval z` is the
subtype of elements lying between the endpoints. The file then equips `Interval z` with the expected
algebraic
structures (nontriviality, order, lattice operations, bounds), and provides a systematic way to
restrict
an “interval measure” `μ` on `ℒ` to an interval measure on `Interval z`.

API design notes:
- `Interval z` is a subtype of `ℒ`, so we provide `CoeOut (Interval z) ℒ` and convenient coercions.
- `Resμ` (and the `Coe` instance for functions) turns a global `μ` into the induced measure on a
  sub-interval.
- Lemmas `μ*_res_intvl` state that the induced constructions (`μmax`, `μmin`, `μA`, `μB`) commute
  with restriction.
- `strip_bot`/`strip_top` are projection lemmas for the endpoints in the interval-as-bounded-order
  view.
-/

namespace HarderNarasimhan

/--
`Interval z` is the subtype of elements of `ℒ` lying between the endpoints of the strict pair `z`.

Mathematically, if `z = (x,y)` with `x < y`, then `Interval z = { p ∈ ℒ | x ≤ p ∧ p ≤ y }`.
We package the endpoints as a sigma-subtype to keep the inequality `x < y` available for typeclass
proofs.
-/
def Interval {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) :=
{p : ℒ // z.val.1 ≤ p ∧ p ≤ z.val.2}


/--
`Interval z` is nontrivial whenever `ℒ` is nontrivial and the endpoints satisfy `x < y`.

API note: we exhibit two distinct elements by using the embedded endpoints `x` and `y`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : Nontrivial (Interval z) where
    exists_pair_ne := ⟨⟨z.val.1, le_rfl, le_of_lt z.prop⟩,
      ⟨z.val.2, le_of_lt z.prop, le_rfl⟩, Subtype.coe_ne_coe.mp <| ne_of_lt z.prop⟩


/--
The order on `Interval z` is inherited from the ambient order on `ℒ` via the subtype coercion.

API note: this is mathlib's standard subtype order.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : PartialOrder (Interval z) :=
  Subtype.partialOrder _


/--
If `ℒ` is a lattice, then `Interval z` is a lattice with `⊔`/`⊓` defined pointwise.

Mathematically, the interval is closed under sup/inf; the closure proofs are discharged
using the endpoint bounds stored in the subtype, and `Subtype.lattice` does the rest.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : Lattice (Interval z) :=
  Subtype.lattice (fun _ _ hx hy ↦ ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩)
    (fun _ _ hx hy ↦ ⟨le_inf hx.1 hy.1, le_trans inf_le_right hy.2⟩)


/--
`Interval z` inherits a bounded order structure: `⊥` is the left endpoint and `⊤` is the right
endpoint.

This turns the interval into a self-contained bounded poset.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : BoundedOrder (Interval z) where
    bot := ⟨z.val.1,⟨le_rfl,le_of_lt z.prop⟩⟩
    bot_le := fun a ↦ a.prop.1
    top := ⟨z.val.2,⟨le_of_lt z.prop,le_rfl⟩⟩
    le_top := fun a ↦ a.prop.2


/--
Coercion from `Interval z` to the ambient type `ℒ`.

API note: `CoeOut` is used so that `a.val` and coercions both work smoothly.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : CoeOut (Interval z) ℒ where
    coe := fun a ↦ a.val


/--
When the interval is the total interval `(⊥, ⊤)`, every element of `ℒ` canonically lies in it.

API note: this coercion lets users reuse lemmas about `Interval TotIntvl` as a “repackaging” of `ℒ`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
Coe ℒ (Interval (⟨(⊥,⊤),bot_lt_top⟩ : {p : ℒ × ℒ // p.1 < p.2})) where
    coe := fun a ↦ ⟨a,⟨bot_le,le_top⟩⟩


/--
Helper lemma: stripping away the interval subtype yields a strict inequality between the underlying
endpoints.

This is used to turn a strict pair in `Interval z` into a strict pair in the ambient `ℒ`.
-/
lemma lt_lt {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} {p : {p :(Interval z) × (Interval z) // p.1 < p.2}} :
(p.val.1.val, p.val.2.val).1 < (p.val.1.val, p.val.2.val).2 :=
  Subtype.coe_lt_coe.mpr p.prop


/--
`Resμ z μ` restricts an interval-indexed function `μ` on `ℒ` to the interval `Interval z`.

Concretely, a strict pair `(a,b)` in `Interval z` maps to the strict pair of their underlying values
in `ℒ`.
This is the core adapter used throughout the development to reuse global constructions on
subintervals.
-/
def Resμ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) {S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
{p :(Interval z) × (Interval z) // p.1 < p.2} → S := fun p ↦ μ ⟨(p.val.1.val,p.val.2.val), lt_lt⟩


/--
Coercion: treat a function `μ` on strict pairs in `ℒ` as a function on strict pairs in `Interval z`
by implicitly restricting via `Resμ`.

API note: this makes downstream statements (e.g. convexity, semistability) reusable on subintervals
without rewriting every occurrence of `μ`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} {S : Type*} [CompleteLattice S] :
Coe ({p :ℒ × ℒ // p.1 < p.2} → S) ({p :(Interval z) × (Interval z) // p.1 < p.2} → S) where
    coe := Resμ z

/--
Well-foundedness is inherited by intervals: if `ℒ` is well-founded with respect to `>` (i.e. no
infinite
strictly descending chains), then so is `Interval z`.

API note: the strict order on `Interval z` is the pullback of the strict order on `ℒ` along
`Subtype.val`, so well-foundedness transports along `InvImage.wf`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [hw : WellFoundedGT ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : WellFoundedGT (Interval z) :=
  ⟨Subrelation.wf (fun h ↦ Subtype.coe_lt_coe.mpr h) (InvImage.wf Subtype.val hw.wf)⟩


/--
Common index-set bijection behind the `_res_intvl` lemmas below: interior points of a strict pair
`J` inside `Interval I` (cut out by a side condition `D`) correspond to interior points of the
underlying strict pair in `ℒ` (cut out by the corresponding ambient condition `C`).

The value function `f` may depend on the ambient membership proof; all proof positions are
handled by proof irrelevance.
-/
private lemma res_intvl_set_eq {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}} {S : Type*} [CompleteLattice S]
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}}
{D : Interval I → Prop} {C : ℒ → Prop}
(hDC : ∀ u : Interval I, InIntvl J u → (D u ↔ C u.val))
(f : (a : ℒ) → InIntvl (⟨(J.val.1.val, J.val.2.val), lt_lt⟩ : {p : ℒ × ℒ // p.1 < p.2}) a ∧
  C a → S) :
{x | ∃ (u : Interval I) (h : InIntvl J u ∧ D u), f u.val ⟨⟨h.1.1, h.1.2⟩, (hDC u h.1).1 h.2⟩ = x} =
{x | ∃ (a : ℒ) (h : InIntvl ⟨(J.val.1.val, J.val.2.val), lt_lt⟩ a ∧ C a), f a h = x} := by
  ext x
  constructor
  · rintro ⟨u, h, rfl⟩
    exact ⟨u.val, ⟨⟨h.1.1, h.1.2⟩, (hDC u h.1).1 h.2⟩, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨a, le_trans J.val.1.prop.1 h.1.1, le_trans h.1.2 J.val.2.prop.2⟩,
      ⟨⟨h.1.1, h.1.2⟩, (hDC _ ⟨h.1.1, h.1.2⟩).2 h.2⟩, rfl⟩

/--
Unfolding lemma for restriction: evaluating `Resμ` is definitionally `μ` on the underlying strict
pair.

API note: written as a lemma to make rewriting with `simp`/`rw` explicit downstream.
-/
lemma μ_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
(Resμ I μ) J = μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= rfl

/--
Restriction commutes with the “left-anchored supremum” construction `μmax` from `Basic.lean`.

Mathematically, taking `μmax` inside an interval is the same as taking `μmax` in `ℒ` after
forgetting
the interval subtype.
-/
lemma μmax_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
μmax (Resμ I μ) J = μmax μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= by
  unfold μmax
  simp only [μ_res_intvl, ne_eq]
  exact congrArg sSup <| res_intvl_set_eq (D := fun u ↦ ¬J.val.1 = u)
    (C := fun a ↦ ¬J.val.1.val = a) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μ ⟨(J.val.1.val, a), lt_of_le_of_ne h.1.1 h.2⟩

/--
Restriction commutes with the “right-anchored infimum” construction `μmin` from `Basic.lean`.

This is the dual statement to `μmax_res_intvl`.
-/
lemma μmin_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
μmin (Resμ I μ) J = μmin μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= by
  unfold μmin
  simp only [μ_res_intvl, ne_eq]
  exact congrArg sInf <| res_intvl_set_eq (D := fun u ↦ ¬u = J.val.2)
    (C := fun a ↦ ¬a = J.val.2.val) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μ ⟨(a, J.val.2.val), lt_of_le_of_ne h.1.2 h.2⟩

/--
Restriction commutes with `μA`, the infimum over right-endpoints of `μmax` values.

This lemma is a key “locality” principle: computations of `μA` can be performed on subintervals.
-/
lemma μA_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
μA (Resμ I μ) J = μA μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= by
  unfold μA
  simp only [μmax_res_intvl, ne_eq]
  exact congrArg sInf <| res_intvl_set_eq (D := fun u ↦ ¬u = J.val.2)
    (C := fun a ↦ ¬a = J.val.2.val) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μmax μ ⟨(a, J.val.2.val), lt_of_le_of_ne h.1.2 h.2⟩

/--
Restriction commutes with `μB`, the supremum over left-endpoints of `μmin` values.

This is the `μB`-analogue of `μA_res_intvl`.
-/
lemma μB_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
μB (Resμ I μ) J = μB μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= by
  unfold μB
  simp only [μmin_res_intvl, ne_eq]
  exact congrArg sSup <| res_intvl_set_eq (D := fun u ↦ ¬J.val.1 = u)
    (C := fun a ↦ ¬J.val.1.val = a) (fun u _ ↦ not_congr Subtype.ext_iff)
    fun a h ↦ μmin μ ⟨(J.val.1.val, a), lt_of_le_of_ne h.1.1 h.2⟩

/--
Projection lemma: the bottom element of `Interval ⟨(a,b), h⟩` is definitionally the left endpoint
`a`.

API note: phrased using `Subtype.val` to make rewriting in proofs convenient.
-/
lemma strip_bot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {a b : ℒ} (h : a < b) :
@Subtype.val ℒ (fun p ↦ a ≤ p ∧ p ≤ b) (⊥: Interval ⟨(a, b), h⟩) = a := rfl

/--
Projection lemma: the top element of `Interval ⟨(a,b), h⟩` is definitionally the right endpoint `b`.
-/
lemma strip_top {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {a b : ℒ} (h : a < b) :
@Subtype.val ℒ (fun p ↦ a ≤ p ∧ p ≤ b) (⊤: Interval ⟨(a, b), h⟩) = b := rfl

end HarderNarasimhan
