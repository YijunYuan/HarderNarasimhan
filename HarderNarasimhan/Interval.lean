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

/-
`Interval z` is the subtype of elements of `ℒ` lying between the endpoints of the strict pair `z`.

Mathematically, if `z = (x,y)` with `x < y`, then `Interval z = { p ∈ ℒ | x ≤ p ∧ p ≤ y }`.
We package the endpoints as a sigma-subtype to keep the inequality `x < y` available for typeclass
proofs.
-/
def Interval {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) :=
{p : ℒ // z.val.1 ≤ p ∧ p ≤ z.val.2}


/-
`Interval z` is nontrivial whenever `ℒ` is nontrivial and the endpoints satisfy `x < y`.

API note: we exhibit two distinct elements by using the embedded endpoints `x` and `y`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : Nontrivial (Interval z) where
    exists_pair_ne := by
        rcases z with ⟨⟨x, y⟩, hxy⟩
        use ⟨x,⟨le_rfl,le_of_lt hxy⟩⟩, ⟨y,⟨le_of_lt hxy,le_rfl⟩⟩
        exact Subtype.coe_ne_coe.mp <| ne_of_lt hxy


/-
The order on `Interval z` is inherited from the ambient order on `ℒ` via the subtype coercion.

API note: this is the standard subtype order; antisymmetry uses `Subtype.ext`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : PartialOrder (Interval z) where
  le := fun a b => a.val ≤ b.val
  le_refl := by (expose_names; exact fun a ↦ Preorder.le_refl a.val)
  le_trans := by
    (expose_names; exact fun a b c a_1 a_2 ↦ Preorder.le_trans a.val b.val c.val a_1 a_2)
  le_antisymm := fun a b h1 h2 ↦ Subtype.ext <| le_antisymm h1 h2


/-
If `ℒ` is a lattice, then `Interval z` is a lattice with `⊔`/`⊓` defined pointwise.

Mathematically, the interval is closed under sup/inf; the proof obligations are discharged
using the endpoint bounds stored in the subtype.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : Lattice (Interval z) where
    sup := fun a b => ⟨a.val ⊔ b.val, ⟨le_trans a.prop.1 le_sup_left,sup_le a.prop.2 b.prop.2⟩⟩
    sup_le := fun _ _ _ h1 h2 ↦ sup_le h1 h2
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right
    inf := fun a b => ⟨a.val ⊓ b.val,⟨le_inf a.prop.1 b.prop.1, le_trans inf_le_right b.prop.2⟩⟩
    le_inf := fun _ _ _ h1 h2 ↦ le_inf h1 h2
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right


/-
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


/-
Coercion from `Interval z` to the ambient type `ℒ`.

API note: `CoeOut` is used so that `a.val` and coercions both work smoothly.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : CoeOut (Interval z) ℒ where
    coe := fun a ↦ a.val


/-
When the interval is the total interval `(⊥, ⊤)`, every element of `ℒ` canonically lies in it.

API note: this coercion lets users reuse lemmas about `Interval TotIntvl` as a “repackaging” of `ℒ`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
Coe ℒ (Interval (⟨(⊥,⊤),bot_lt_top⟩ : {p : ℒ × ℒ // p.1 < p.2})) where
    coe := fun a ↦ ⟨a,⟨bot_le,le_top⟩⟩


/-
Helper lemma: stripping away the interval subtype yields a strict inequality between the underlying
endpoints.

This is used to turn a strict pair in `Interval z` into a strict pair in the ambient `ℒ`.
-/
lemma lt_lt {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} {p : {p :(Interval z) × (Interval z) // p.1 < p.2}} :
(p.val.1.val, p.val.2.val).1 < (p.val.1.val, p.val.2.val).2 := by
  refine Subtype.coe_lt_coe.mpr ?_
  refine Subtype.mk_lt_mk.2 (lt_iff_le_not_ge.mpr p.prop)


/-
`Resμ z μ` restricts an interval-indexed function `μ` on `ℒ` to the interval `Interval z`.

Concretely, a strict pair `(a,b)` in `Interval z` maps to the strict pair of their underlying values
in `ℒ`.
This is the core adapter used throughout the development to reuse global constructions on
subintervals.
-/
def Resμ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) {S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
{p :(Interval z) × (Interval z) // p.1 < p.2} → S := fun p ↦ μ ⟨(p.val.1.val,p.val.2.val), lt_lt⟩


/-
Coercion: treat a function `μ` on strict pairs in `ℒ` as a function on strict pairs in `Interval z`
by implicitly restricting via `Resμ`.

API note: this makes downstream statements (e.g. convexity, semistability) reusable on subintervals
without rewriting every occurrence of `μ`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} {S : Type*} [CompleteLattice S] :
Coe ({p :ℒ × ℒ // p.1 < p.2} → S) ({p :(Interval z) × (Interval z) // p.1 < p.2} → S) where
    coe := Resμ z

/-
Well-foundedness is inherited by intervals: if `ℒ` is well-founded with respect to `>` (i.e. no
infinite
strictly descending chains), then so is `Interval z`.

API note: we prove the “has minimum” characterization by mapping a nonempty set in `Interval z` to
its image
in `ℒ`, taking a minimum there, and transporting it back.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [hw : WellFoundedGT ℒ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : WellFoundedGT (Interval z) := by
    refine { wf := WellFounded.wellFounded_iff_has_min.mpr fun S hS ↦ ?_ }
    rcases hw.wf.has_min (Subtype.val '' S) ( Set.Nonempty.image Subtype.val hS) with ⟨a,ha⟩
    have := ha.1
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at this
    rcases this with ⟨x, hx⟩
    exact Exists.intro ⟨a, x⟩ ⟨hx, fun y hy h ↦ ha.right y.val
      (Set.mem_image_of_mem Subtype.val hy) (lt_iff_le_not_ge.2 h)⟩


/-
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

/-
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
  congr
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use u.val
    use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.1 hc)⟩
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use ⟨u,le_trans ((J.val).1.prop.1) hu1.1.1
      ,le_trans hu1.1.2 ((J.val).2.prop.2)⟩
    rw [← hu2]
    simp only [exists_prop, and_true]
    exact ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.2 hc)⟩

/-
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
  congr
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use u.val
    use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.1 hc)⟩
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use ⟨u,le_trans ((J.val).1.prop.1) hu1.1.1
      ,le_trans hu1.1.2 ((J.val).2.prop.2)⟩
    rw [← hu2]
    simp only [exists_prop, and_true]
    exact ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.2 hc)⟩

/-
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
  congr
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use u.val
    use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.1 hc)⟩
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use ⟨u,le_trans ((J.val).1.prop.1) hu1.1.1
      ,le_trans hu1.1.2 ((J.val).2.prop.2)⟩
    rw [← hu2]
    simp only [exists_prop, and_true]
    exact ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.2 hc)⟩

/-
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
  congr
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use u.val
    use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.1 hc)⟩
  · intro hx
    rcases hx with ⟨u,hu1,hu2⟩
    use ⟨u,le_trans ((J.val).1.prop.1) hu1.1.1
      ,le_trans hu1.1.2 ((J.val).2.prop.2)⟩
    rw [← hu2]
    simp only [exists_prop, and_true]
    exact ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.2 hc)⟩

/-
Projection lemma: the bottom element of `Interval ⟨(a,b), h⟩` is definitionally the left endpoint
`a`.

API note: phrased using `Subtype.val` to make rewriting in proofs convenient.
-/
lemma strip_bot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {a b : ℒ} (h : a < b) :
@Subtype.val ℒ (fun p ↦ a ≤ p ∧ p ≤ b) (⊥: Interval ⟨(a, b), h⟩) = a := rfl

/-
Projection lemma: the top element of `Interval ⟨(a,b), h⟩` is definitionally the right endpoint `b`.
-/
lemma strip_top {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {a b : ℒ} (h : a < b) :
@Subtype.val ℒ (fun p ↦ a ≤ p ∧ p ≤ b) (⊤: Interval ⟨(a, b), h⟩) = b := rfl

end HarderNarasimhan
