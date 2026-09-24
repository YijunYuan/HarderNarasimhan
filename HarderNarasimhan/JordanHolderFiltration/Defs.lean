/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.FirstMoverAdvantage.Defs
public import Mathlib.Data.Rel

/-!
# Section 4.5: definitions of Jordan–Hölder filtrations

The hypotheses of Theorem 4.25 and the filtration named in Remark 4.26 are packaged as
typeclasses and a structure. The chain is indexed by natural numbers and extended
constantly by `⊥` after its length. See `Results` for the statements and `Impl` for proofs.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Classes

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Theorem 4.25: the finite-total-payoff hypothesis, packaged as an auxiliary typeclass.
A payoff function has finite total payoff if the payoff of the interval with endpoints
`⊥` and `⊤` differs from `⊤`. -/
class FiniteTotalPayoff (μ : PayoffFunction ℒ S) : Prop where
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The total payoff is not `⊤`. -/
  ne_top : μ ⊤ ≠ ⊤

/-- Theorem 4.25, hypothesis (ii) of Section 4.5, packaged as an auxiliary typeclass.
Every infinite strictly decreasing chain has a successive interval of payoff `⊤`.

Together with finite total payoff, this condition ensures that a chain whose steps all
have the total payoff cannot decrease strictly forever. -/
class EventuallyTopDCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  Some step of every strictly descending chain has payoff `⊤`. -/
  exists_eq_top : ∀ x : ℕ → ℒ, (hx : StrictAnti x) →
    ∃ N : ℕ, μ ⟨x (N + 1), x N, hx (Nat.lt_succ_self N)⟩ = ⊤

variable {μ : PayoffFunction ℒ S}

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The eventually-`⊤` descending chain condition implies the strong descending chain condition. -/
instance [h : μ.EventuallyTopDCC] : μ.StrongDCC where
  exists_le f saf := let ⟨N, hN⟩ := h.exists_eq_top f saf; ⟨N, hN ▸ le_top⟩

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The eventually-`⊤` condition is stable under restriction to a subinterval. -/
instance [h : μ.EventuallyTopDCC] {I : StrictIntvl ℒ} : (μ.restrict I).EventuallyTopDCC where
  exists_eq_top f saf := h.exists_eq_top (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ saf hn

end Classes

section JordanHolderFiltration

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Remark 4.26: the Jordan–Hölder filtration defined by the conditions of Theorem 4.25.
A Jordan–Hölder filtration of `μ` is a finite strictly decreasing chain from `⊤` to `⊥`
whose successive intervals have payoff `μ ⊤`. Replacing the upper endpoint of a step by a
strictly intermediate point must strictly decrease its payoff.

The chain is indexed by `ℕ` and is constantly `⊥` from `length` onwards. -/
structure JordanHolderFiltration (μ : PayoffFunction ℒ S) where
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The underlying chain. -/
  toFun : ℕ → ℒ
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The number of strict steps in the chain. -/
  length : ℕ
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The chain is antitone. -/
  antitone : Antitone toFun
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The chain starts at `⊤`. -/
  head_eq_top : toFun 0 = ⊤
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The chain reaches `⊥` at index `length`. -/
  length_eq_bot : toFun length = ⊥
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  The chain is strictly decreasing up to `length`. -/
  strictAntiOn : StrictAntiOn toFun (Set.Iic length)
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  Each successive step `(F (i + 1), F i)` carries the total payoff `μ ⊤`. -/
  step_payoff_eq : ∀ i, (hi : i < length) →
    μ ⟨toFun (i + 1), toFun i, strictAntiOn hi.le hi (Nat.lt_succ_self i)⟩ = μ ⊤
  /-- Auxiliary API for Theorem 4.25 and Remark 4.26.
  Replacing the upper endpoint of a step by a strictly intermediate point strictly
  decreases its payoff. -/
  payoff_lt_of_between : ∀ i, (hi : i < length) → ∀ z : ℒ, (h' : toFun (i + 1) < z) →
    z < toFun i →
    μ ⟨toFun (i + 1), z, h'⟩ <
      μ ⟨toFun (i + 1), toFun i, strictAntiOn hi.le hi (Nat.lt_succ_self i)⟩

namespace JordanHolderFiltration

variable {μ : PayoffFunction ℒ S}

/-- Auxiliary coercion for Remark 4.26: a filtration is determined by its chain. -/
instance : FunLike (μ.JordanHolderFiltration) ℕ ℒ where
  coe := toFun
  coe_injective := by
    have key : ∀ F G : μ.JordanHolderFiltration, F.toFun = G.toFun →
        F.length ≤ G.length := by
      intro F G h
      by_contra hc
      rw [not_le] at hc
      have h1 := F.strictAntiOn hc.le (Set.mem_Iic.2 le_rfl) hc
      rw [F.length_eq_bot, h, G.length_eq_bot] at h1
      exact lt_irrefl ⊥ h1
    intro F G h
    have hlen : F.length = G.length := le_antisymm (key F G h) (key G F h.symm)
    cases F; cases G
    dsimp only at h hlen
    subst h; subst hlen
    rfl

/-- Auxiliary API for Remark 4.26: the coercion agrees with the underlying chain. -/
@[simp] lemma toFun_eq_coe (F : μ.JordanHolderFiltration) : F.toFun = ⇑F := rfl

variable {F G : μ.JordanHolderFiltration} {m : ℕ}

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The first term is `⊤`. -/
@[simp] lemma apply_zero (F : μ.JordanHolderFiltration) : F 0 = ⊤ := F.head_eq_top

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The term at index `length` is `⊥`. -/
@[simp] lemma apply_length (F : μ.JordanHolderFiltration) : F F.length = ⊥ := F.length_eq_bot

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Below `F.length` the chain lies strictly above `⊥`. -/
lemma bot_lt_of_lt (h : m < F.length) : ⊥ < F m :=
  F.length_eq_bot ▸ F.strictAntiOn h.le (Set.mem_Iic.2 le_rfl) h

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Below `F.length` the chain has not yet reached `⊥`. -/
lemma ne_bot_of_lt (h : m < F.length) : F m ≠ ⊥ := (bot_lt_of_lt h).ne'

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The length is the least index at which the filtration reaches `⊥`. -/
lemma length_le_of_eq_bot (h : F m = ⊥) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_bot_of_lt hc h

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
From `F.length` onwards, the chain is constantly `⊥`. -/
lemma eq_bot_of_length_le (h : F.length ≤ m) : F m = ⊥ :=
  le_bot_iff.1 <| F.length_eq_bot ▸ F.antitone h

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
A term differs from `⊥` if and only if its index is less than the length. -/
lemma ne_bot_iff_lt_length : F m ≠ ⊥ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_bot_of_length_le hc), ne_bot_of_lt⟩

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Each term above `⊥` is strictly greater than its successor. -/
lemma succ_lt_of_ne_bot (h : F m ≠ ⊥) : F (m + 1) < F m := by
  have hm : m < F.length := ne_bot_iff_lt_length.1 h
  exact F.strictAntiOn hm.le hm (Nat.lt_succ_self m)

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
A Jordan–Hölder filtration of a nontrivial order has positive length. -/
lemma length_pos (F : μ.JordanHolderFiltration) : 0 < F.length :=
  Nat.pos_of_ne_zero fun h ↦
    top_ne_bot (α := ℒ) (F.head_eq_top.symm.trans (h ▸ F.length_eq_bot))

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Filtration terms strictly decrease up to `F.length`. -/
lemma apply_lt_apply {i j : ℕ} (hij : i < j) (hj : j ≤ F.length) : F j < F i :=
  F.strictAntiOn (hij.le.trans hj) hj hij

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Strictly after the start and up to `F.length`, the chain lies strictly below `⊤`. -/
lemma apply_lt_top (h0 : 0 < m) (hm : m ≤ F.length) : F m < ⊤ :=
  F.apply_zero ▸ apply_lt_apply h0 hm

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Each successive interval has the total payoff. -/
lemma step_payoff (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) :
    μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (Nat.lt_succ_self i)⟩ = μ ⊤ :=
  F.step_payoff_eq i hi

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Replacing the upper endpoint of a step by a strictly intermediate point strictly
decreases its payoff. -/
lemma payoff_lt (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) {z : ℒ}
    (h' : F (i + 1) < z) (h'' : z < F i) :
    μ ⟨F (i + 1), z, h'⟩ < μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (Nat.lt_succ_self i)⟩ :=
  F.payoff_lt_of_between i hi z h' h''

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
Two Jordan–Hölder filtrations are equal if they agree at every index. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end JordanHolderFiltration

end JordanHolderFiltration

section JordanHolderRel

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Auxiliary API for Theorem 4.25 and Remark 4.26.
The relation between `x` and `y < x` for which the interval with endpoints `y` and `x`
has payoff `μ ⊤`, and replacing `x` by any strictly intermediate point gives a smaller payoff.

A finite series for this relation from `⊤` to `⊥` gives a Jordan–Hölder filtration. -/
def jordanHolderRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : y < x, μ ⟨y, x, h⟩ = μ ⊤ ∧
    ∀ z : ℒ, (h' : y < z) → z < x → μ ⟨y, z, h'⟩ < μ ⟨y, x, h⟩}

end JordanHolderRel

end PayoffFunction

end HarderNarasimhan
