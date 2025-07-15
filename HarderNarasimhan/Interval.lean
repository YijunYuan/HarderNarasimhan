import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Sublattice


def Interval {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(z : {p : ℒ × ℒ // p.1 < p.2}) : Type :=
{p : ℒ // z.val.1 ≤ p ∧ p ≤ z.val.2}


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : Nontrivial (Interval z) where
    exists_pair_ne := by
        rcases z with ⟨⟨x, y⟩, hxy⟩
        use ⟨x,⟨le_rfl,le_of_lt hxy⟩⟩, ⟨y,⟨le_of_lt hxy,le_rfl⟩⟩
        exact Subtype.coe_ne_coe.mp <| ne_of_lt hxy


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : Lattice (Interval z) where
    le := fun a b => a.val ≤ b.val
    le_refl := by (expose_names; exact fun a ↦ Preorder.le_refl a.val)
    le_trans := by  (expose_names; exact fun a b c a_1 a_2 ↦ Preorder.le_trans a.val b.val c.val a_1 a_2)
    le_antisymm := fun a b h1 h2 ↦ Subtype.ext <| le_antisymm h1 h2
    sup := fun a b => ⟨a.val ⊔ b.val, ⟨le_trans a.prop.1 le_sup_left,sup_le a.prop.2 b.prop.2⟩⟩
    sup_le := fun a b c h1 h2 ↦ sup_le h1 h2
    le_sup_left := fun a b ↦ le_sup_left
    le_sup_right := fun a b ↦ le_sup_right
    inf := fun a b => ⟨a.val ⊓ b.val,⟨le_inf a.prop.1 b.prop.1, le_trans inf_le_right b.prop.2⟩⟩
    le_inf := fun a b c h1 h2 ↦ le_inf h1 h2
    inf_le_left := fun a b ↦ inf_le_left
    inf_le_right := fun a b ↦ inf_le_right


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : BoundedOrder (Interval z) where
    bot := ⟨z.val.1,⟨le_rfl,le_of_lt z.prop⟩⟩
    bot_le := fun a ↦ a.prop.1
    top := ⟨z.val.2,⟨le_of_lt z.prop,le_rfl⟩⟩
    le_top := fun a ↦ a.prop.2


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} : CoeOut (Interval z) ℒ where
    coe := fun a ↦ a.val


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] : Coe ℒ (Interval (⟨(⊥,⊤),bot_lt_top⟩ : {p : ℒ × ℒ // p.1 < p.2})) where
    coe := fun a ↦ ⟨a,⟨bot_le,le_top⟩⟩


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {z : {p : ℒ × ℒ // p.1 < p.2}} {S : Type} [CompleteLattice S] : Coe ({p :ℒ × ℒ // p.1 < p.2} → S) ({p :(Interval z) × (Interval z) // p.1 < p.2} → S) where
    coe := fun μ ↦ (fun p ↦ μ ⟨(p.val.1.val,p.val.2.val),Subtype.GCongr.coe_lt_coe <| Subtype.mk_lt_mk.2 (lt_iff_le_not_le.mpr p.prop)⟩)
