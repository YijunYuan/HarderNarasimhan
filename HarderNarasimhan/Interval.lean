import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Sublattice

@[ext]
structure Interval (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) where
    val  : ℒ
    x_le : x ≤ val
    le_y : val ≤ y

instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) : LE (Interval ℒ x y h) where
    le a b := a.val ≤ b.val

instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) : LT (Interval ℒ x y h) where
    lt a b := a.val < b.val

instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) : BoundedOrder (Interval ℒ x y h) where
    top := Interval.mk y h (le_refl y)
    le_top := by intro z; apply z.le_y
    bot := Interval.mk x (le_refl x) h
    bot_le := by intro z; apply z.x_le

instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) : PartialOrder (Interval ℒ x y h) where
    le := (· ≤ ·)
    lt := (· < ·)
    le_refl := by intros; apply le_refl
    le_trans := by intros; expose_names; exact Preorder.le_trans a.val b.val c.val h_1 h_2
    lt_iff_le_not_le := by intros; apply lt_iff_le_not_le
    le_antisymm := by intros; ext; expose_names; exact PartialOrder.le_antisymm a.val b.val h_1 h_2

instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) : CoeOut (Interval ℒ x y h) ℒ where
    coe := Interval.val

--instance (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y) (S : Type) [CompleteLattice S] : CoeOut (ℒ × ℒ → S) ((Interval ℒ x y h) × (Interval ℒ x y h) → S) :=
--    coe := fun μ => fun a => μ (a.1, a.2)
---------------------------------------
variable (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (x: ℒ) (y: ℒ) (h: x ≤ y)
variable (a : Interval ℒ x y h) (b : Interval ℒ x y h)
#check a ≤ b
#check OrderTop (Interval ℒ x y h)
#check Interval.mk




def InInterval {ℒ: Type} [PartialOrder ℒ]
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) : Prop :=
  I.val.1 ≤ x ∧ x ≤ I.val.2
