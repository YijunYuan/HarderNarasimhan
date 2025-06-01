import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

import HarderNarasimhan.Interval

def VAI {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (x : ℒ) : Set S :=
μ '' {p : {q : ℒ × ℒ // q.1 < q.2} | p.val.1 = x ∧ InInterval I x ∧ InInterval I p.val.2 ∧ x < p.val.2}

def μmax {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup (VAI μ ⟨(⊥ , I.val.2),lt_of_le_of_lt bot_le I.prop⟩ I.val.1)

def μA {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}): S :=
sInf {μmax μ ⟨(a , I.val.2),(lt_of_le_of_ne ha.left.right ha.2)⟩ | (a : ℒ) (ha : InInterval I a ∧ a ≠ I.val.2)}

def μAstar (ℒ : Type) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : S :=
μA μ ⟨(⊥,⊤) , bot_lt_top⟩
