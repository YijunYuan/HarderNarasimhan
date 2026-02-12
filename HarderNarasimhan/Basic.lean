import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic

namespace HarderNarasimhan

def InIntvl {ℒ : Type*} [PartialOrder ℒ]
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) : Prop :=
  I.val.1 ≤ x ∧ x ≤ I.val.2


abbrev TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
{p : ℒ × ℒ // p.1 < p.2} := ⟨(⊥,⊤),bot_lt_top⟩


lemma in_TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (x : ℒ) :
InIntvl TotIntvl x := ⟨bot_le,le_top⟩


def μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup {μ ⟨(I.val.1 , u), lt_of_le_of_ne h.1.1 h.2⟩ | (u : ℒ) (h : InIntvl I u ∧ I.val.1 ≠ u) }


def μA {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sInf {μmax μ ⟨(a , I.val.2),(lt_of_le_of_ne ha.1.2 ha.2)⟩ |
  (a : ℒ) (ha : InIntvl I a ∧ a ≠ I.val.2)}


def μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : S :=
μA μ ⟨(⊥,⊤) , bot_lt_top⟩


def μmin {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sInf {μ ⟨(u, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩ | (u : ℒ) (h : InIntvl I u ∧ u ≠ I.val.2) }


def μB {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup {μmin μ ⟨(I.val.1 , a),(lt_of_le_of_ne ha.1.1 ha.2)⟩ |
  (a : ℒ) (ha : InIntvl I a ∧ I.val.1 ≠ a)}


def μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : S :=
μB μ ⟨(⊥,⊤) , bot_lt_top⟩


def IsComparable {ℒ : Type*} [PartialOrder ℒ] : (x : ℒ) → (y : ℒ) → Prop :=
  fun x y => x ≤ y ∨ y ≤ x


def IsAttained {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
  ∃ (a : ℒ) (haI : InIntvl I a) (ha : a ≠ I.val.2),
    μmax μ ⟨(a , I.val.2) , lt_of_le_of_ne haI.2 ha⟩ = μA μ I

end HarderNarasimhan
