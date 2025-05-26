import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

import HarderNarasimhan.Interval

-- VAI does `NOT` make sense if `IBot ≤ x ∧ x < ITop` is not satisfied.
def VAI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (IBot : ℒ) (ITop : ℒ) (x : ℒ) : Set S := μ '' {p : ℒ × ℒ | p.1 = x ∧ (IBot ≤ x ∧ x < ITop) ∧ (IBot ≤ p.2 ∧ p.2 ≤ ITop) ∧ x < p.2}

-- μmaxI does `NOT` make sense if `I.1 < I.2` is not satisfied.
def μmaxI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) : S := sSup (VAI ℒ S μ ⊥ I.2 I.1)

-- μAI does `NOT` make sense if `I.1 < I.2` is not satisfied.
def μAI (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) : S := sInf {μmaxI ℒ S μ (a,I.2) | (a : ℒ) (_ : I.1 ≤ a ∧ a < I.2)}

def μAstar (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : S := μAI ℒ S μ (⊥,⊤)


--def supVₐ (ℒ: Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (x : ℒ) : S := sSup (Vₐ ℒ S μ x)

--def μₐ (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : S :=
--  sInf {(supVₐ ℒ S μ) a| a ≠ ⊤}

--def μmax (ℒ : Type) [PartialOrder ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (a : ℒ) (y : ℒ) : S := sSup (μ '' { p : ℒ × ℒ | p.1 = a ∧ p.1 < p.2 ∧ p.2 ≤ y})

---------------------------------------
variable (G : Type) [Group G]
variable (H: Subgroup G)

def fuck (G : Type) [Group G] : ℕ := 1

#check fuck H
