import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

import HarderNarasimhan.Interval

-- VAI does `NOT` make sense if `IBot ≤ x ∧ x < ITop` is not satisfied.
def VAI {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (x : ℒ) : Set S :=
μ '' {p : ℒ × ℒ | p.1 = x ∧ InInterval I x ∧ InInterval I p.2 ∧ x < p.2}

-- μmax does `NOT` make sense if `I.1 < I.2` is not satisfied.
def μmax {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup (VAI μ ⟨(⊥ , I.val.2),lt_of_le_of_lt bot_le I.prop⟩ I.val.1)

-- μA does `NOT` make sense if `I.1 < I.2` is not satisfied.
def μA {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2}): S :=
sInf {μmax μ ⟨(a , I.val.2),(lt_of_le_of_ne ha.left.right ha.2)⟩ | (a : ℒ) (ha : InInterval I a ∧ a ≠ I.val.2)}

def μAstar (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : ℒ × ℒ → S) : S :=
μA μ ⟨(⊥,⊤) , bot_lt_top⟩

--def supVₐ (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (x : ℒ) : S := sSup (Vₐ ℒ S μ x)

--def μₐ (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : S :=
--  sInf {(supVₐ ℒ S μ) a| a ≠ ⊤}

--def μmax (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (a : ℒ) (y : ℒ) : S := sSup (μ '' { p : ℒ × ℒ | p.1 = a ∧ p.1 < p.2 ∧ p.2 ≤ y})

---------------------------------------
variable (G : Type) [Group G]
variable (H: Subgroup G)

def fuck (G : Type) [Group G] : ℕ := 1

#check fuck H
