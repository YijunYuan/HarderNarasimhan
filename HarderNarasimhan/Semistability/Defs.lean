import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Interval

namespace HarderNarasimhan

class μA_DescendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  μ_dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μA μ ⟨(a, f N), h₁ N⟩ < μA μ ⟨(a, f <| N + 1), h₁ <| N + 1⟩


def S₁I {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x) : Prop :=
∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) →
  ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ >
    μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩


def S₂I {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x) : Prop :=
∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) →
  μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ =
  μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.1 hx⟩ → y ≤ x


def StI {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Set ℒ :=
{l : ℒ | ∃ hlI : InIntvl I l , ∃ hl : I.val.1 ≠ l ,  (S₁I μ I l hlI hl) ∧ (S₂I μ I l hlI hl)}


def St {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Set ℒ :=
StI μ TotIntvl


def semistableI {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := I.val.2 ∈ StI μ I


class Semistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  semistable : ∀x : ℒ, (hx : x ≠ ⊥) →
    ¬ μA μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ > μA μ ⟨(⊥,⊤),bot_lt_top⟩

class Stable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) extends Semistable μ where
  stable : ∀x : ℒ, (hx : x ≠ ⊥) → x ≠ ⊤ →
    μA μ ⟨(⊥,x), bot_lt_iff_ne_bot.2 hx⟩ ≠ μA μ ⟨(⊥,⊤),bot_lt_top⟩

end HarderNarasimhan
