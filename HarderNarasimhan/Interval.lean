import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Sublattice

import HarderNarasimhan.Basic

namespace HarderNarasimhan
def Interval {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) :=
{p : ℒ // z.val.1 ≤ p ∧ p ≤ z.val.2}


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : Nontrivial (Interval z) where
    exists_pair_ne := by
        rcases z with ⟨⟨x, y⟩, hxy⟩
        use ⟨x,⟨le_rfl,le_of_lt hxy⟩⟩, ⟨y,⟨le_of_lt hxy,le_rfl⟩⟩
        exact Subtype.coe_ne_coe.mp <| ne_of_lt hxy


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : PartialOrder (Interval z) where
  le := fun a b => a.val ≤ b.val
  le_refl := by (expose_names; exact fun a ↦ Preorder.le_refl a.val)
  le_trans := by  (expose_names; exact fun a b c a_1 a_2 ↦ Preorder.le_trans a.val b.val c.val a_1 a_2)
  le_antisymm := fun a b h1 h2 ↦ Subtype.ext <| le_antisymm h1 h2


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : Lattice (Interval z) where
    sup := fun a b => ⟨a.val ⊔ b.val, ⟨le_trans a.prop.1 le_sup_left,sup_le a.prop.2 b.prop.2⟩⟩
    sup_le := fun _ _ _ h1 h2 ↦ sup_le h1 h2
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right
    inf := fun a b => ⟨a.val ⊓ b.val,⟨le_inf a.prop.1 b.prop.1, le_trans inf_le_right b.prop.2⟩⟩
    le_inf := fun _ _ _ h1 h2 ↦ le_inf h1 h2
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : BoundedOrder (Interval z) where
    bot := ⟨z.val.1,⟨le_rfl,le_of_lt z.prop⟩⟩
    bot_le := fun a ↦ a.prop.1
    top := ⟨z.val.2,⟨le_of_lt z.prop,le_rfl⟩⟩
    le_top := fun a ↦ a.prop.2


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : CoeOut (Interval z) ℒ where
    coe := fun a ↦ a.val


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] : Coe ℒ (Interval (⟨(⊥,⊤),bot_lt_top⟩ : {p : ℒ × ℒ // p.1 < p.2})) where
    coe := fun a ↦ ⟨a,⟨bot_le,le_top⟩⟩


lemma lt_lt {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} {p : {p :(Interval z) × (Interval z) // p.1 < p.2}} : (p.val.1.val, p.val.2.val).1 < (p.val.1.val, p.val.2.val).2 := by
  refine Subtype.coe_lt_coe.mpr ?_
  refine Subtype.mk_lt_mk.2 (lt_iff_le_not_ge.mpr p.prop)


def Resμ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (z : {p : ℒ × ℒ // p.1 < p.2}) {S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S): {p :(Interval z) × (Interval z) // p.1 < p.2} → S := fun p ↦ μ ⟨(p.val.1.val,p.val.2.val), lt_lt⟩


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} {S : Type*} [CompleteLattice S] : Coe ({p :ℒ × ℒ // p.1 < p.2} → S) ({p :(Interval z) × (Interval z) // p.1 < p.2} → S) where
    coe := Resμ z

instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [hw : WellFoundedGT ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : WellFoundedGT (Interval z) := by
    refine { wf := WellFounded.wellFounded_iff_has_min.mpr fun S hS ↦ ?_ }
    rcases hw.wf.has_min (Subtype.val '' S) ( Set.Nonempty.image Subtype.val hS) with ⟨a,ha⟩
    have := ha.1
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at this
    rcases this with ⟨x, hx⟩
    exact Exists.intro ⟨a, x⟩ ⟨hx, fun y hy h ↦ ha.right y.val (Set.mem_image_of_mem Subtype.val hy) (lt_iff_le_not_ge.2 h)⟩

lemma μ_res_intvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}}
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
{J : {p :(Interval I) × (Interval I) // p.1 < p.2}} :
------------
(Resμ I μ) J = μ ⟨(J.val.1.val,J.val.2.val),lt_lt⟩
------------
:= rfl

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

end HarderNarasimhan
