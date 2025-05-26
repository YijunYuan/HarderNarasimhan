import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

import HarderNarasimhan.Interval

def VAI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (IBot : ℒ) (ITop : ℒ) (x : ℒ) (_ : IBot ≤ x ∧ x < ITop) : Set S := μ '' {p : ℒ × ℒ | p.1 = x ∧ (IBot ≤ p.2 ∧ p.2 ≤ ITop) ∧ p.1 < p.2}

def μmaxI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (a : ℒ) (y : ℒ) (h : a < y) : S := sSup (VAI ℒ S μ ⊥ y a ⟨bot_le,h⟩)

def μAI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (IBot : ℒ) (ITop : ℒ) (_ : IBot < ITop) : S := sInf {μmaxI ℒ S μ a ITop ha.2 | (a : ℒ) (ha : IBot ≤ a ∧ a < ITop)}

def μAstar (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : S := μAI ℒ S μ ⊥ ⊤ bot_lt_top


--def supVₐ (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (x : ℒ) : S := sSup (Vₐ ℒ S μ x)

--def μₐ (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : S :=
--  sInf {(supVₐ ℒ S μ) a| a ≠ ⊤}

--def μmax (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (a : ℒ) (y : ℒ) : S := sSup (μ '' { p : ℒ × ℒ | p.1 = a ∧ p.1 < p.2 ∧ p.2 ≤ y})

---------------------------------------
variable (G : Type) [Group G]
variable (H: Subgroup G)

def fuck (G : Type) [Group G] : ℕ := 1

#check fuck H
