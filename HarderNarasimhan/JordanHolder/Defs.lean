/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.NashEquilibrium
public import HarderNarasimhan.PayoffFunction.SlopeLike
public import Mathlib.Data.Rel

/-!
# Jordan–Hölder filtrations

A Jordan–Hölder filtration of a payoff function `μ` is a finite chain
`⊤ = F 0 > F 1 > ⋯ > F F.length = ⊥`. Each successive interval has payoff `μ ⊤`, and
replacing its upper endpoint by a strictly intermediate point strictly decreases the payoff.
For slope-like payoff functions with a complete linearly ordered codomain, the strict
inequality condition is equivalent to stability of each step under the chain hypotheses of
`HarderNarasimhan/JordanHolder/Stability.lean`.

Existence is proved in `HarderNarasimhan/JordanHolder/Exists.lean`. Filtrations need not be
unique, but their length is unique for affine payoff functions on modular lattices under
the hypotheses of `HarderNarasimhan/JordanHolder/Length.lean`.

## Main definitions

* `HarderNarasimhan.PayoffFunction.FiniteTotalPayoff`: the total payoff `μ ⊤` differs from `⊤`.
* `HarderNarasimhan.PayoffFunction.EventuallyTopDCC`: every infinite strictly decreasing
  chain has a successive interval of payoff `⊤`.
* `HarderNarasimhan.PayoffFunction.JordanHolderFiltration`: a Jordan–Hölder filtration.
* `HarderNarasimhan.PayoffFunction.jordanHolderRel`: the relation describing its steps.

## Implementation notes

Filtrations are indexed by `ℕ` and extended constantly by `⊥` from `F.length` onwards.
The length is determined by the underlying function: it is the first index at which the
filtration reaches `⊥`. Thus equality of filtrations is pointwise equality.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Classes

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A payoff function has finite total payoff if the payoff of the interval with endpoints
`⊥` and `⊤` differs from `⊤`. -/
class FiniteTotalPayoff (μ : PayoffFunction ℒ S) : Prop where
  /-- The total payoff is not `⊤`. -/
  ne_top : μ ⊤ ≠ ⊤

/-- Every infinite strictly decreasing chain has a successive interval of payoff `⊤`.

Together with finite total payoff, this condition ensures that a chain whose steps all
have the total payoff cannot decrease strictly forever. -/
class EventuallyTopDCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Some step of every strictly descending chain has payoff `⊤`. -/
  exists_eq_top : ∀ x : ℕ → ℒ, (hx : StrictAnti x) →
    ∃ N : ℕ, μ ⟨x (N + 1), x N, hx (lt_add_one N)⟩ = ⊤

variable {μ : PayoffFunction ℒ S}

/-- The eventually-`⊤` descending chain condition implies the strong descending chain condition. -/
instance [h : μ.EventuallyTopDCC] : μ.StrongDCC where
  exists_le f saf := let ⟨N, hN⟩ := h.exists_eq_top f saf; ⟨N, hN ▸ le_top⟩

/-- The eventually-`⊤` condition is stable under restriction to a subinterval. -/
instance [h : μ.EventuallyTopDCC] {I : StrictIntvl ℒ} : (μ.restrict I).EventuallyTopDCC where
  exists_eq_top f saf := h.exists_eq_top (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ saf hn

end Classes

section RestrictBotFiniteTotalPayoff

variable [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- For a semistable slope-like payoff function with a complete linearly ordered codomain,
finite total payoff is inherited by restrictions to intervals with left endpoint `⊥`,
under the ascending and eventually-`⊤` descending chain conditions. -/
instance [hftp : μ.FiniteTotalPayoff] [μ.IsSlopeLike] [hst : μ.IsSemistable]
    [μ.EventuallyTopDCC] {x : ℒ} {hx : ⊥ < x} :
    (μ.restrict ⟨⊥, x, hx⟩).FiniteTotalPayoff where
  ne_top := by
    simp only [restrict_apply, StrictIntvl.ofSub_top]
    intro h
    have hmax : μ.max ⊤ = μ ⊤ :=
      max_top_eq_apply_iff.2
        (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
    have hq : μ ⟨⊥, x, hx⟩ ≤ μ ⊤ := hmax ▸ le_max (I := ⊤) ⟨hx, le_top⟩
    exact hftp.ne_top (top_le_iff.1 (h ▸ hq))

end RestrictBotFiniteTotalPayoff

section JordanHolderFiltration

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A Jordan–Hölder filtration of `μ` is a finite strictly decreasing chain from `⊤` to `⊥`
whose successive intervals have payoff `μ ⊤`. Replacing the upper endpoint of a step by a
strictly intermediate point must strictly decrease its payoff.

The chain is indexed by `ℕ` and is constantly `⊥` from `length` onwards. -/
structure JordanHolderFiltration (μ : PayoffFunction ℒ S) where
  /-- The underlying chain. -/
  toFun : ℕ → ℒ
  /-- The number of strict steps in the chain. -/
  length : ℕ
  /-- The chain is antitone. -/
  antitone : Antitone toFun
  /-- The chain starts at `⊤`. -/
  head_eq_top : toFun 0 = ⊤
  /-- The chain reaches `⊥` at index `length`. -/
  length_eq_bot : toFun length = ⊥
  /-- The chain is strictly decreasing up to `length`. -/
  strictAntiOn : StrictAntiOn toFun (Set.Iic length)
  /-- Each successive step `(F (i + 1), F i)` carries the total payoff `μ ⊤`. -/
  step_payoff_eq : ∀ i, (hi : i < length) →
    μ ⟨toFun (i + 1), toFun i, strictAntiOn hi.le hi (lt_add_one i)⟩ = μ ⊤
  /-- Replacing the upper endpoint of a step by a strictly intermediate point strictly
  decreases its payoff. -/
  payoff_lt_of_between : ∀ i, (hi : i < length) → ∀ z : ℒ, (h' : toFun (i + 1) < z) →
    z < toFun i →
    μ ⟨toFun (i + 1), z, h'⟩ <
      μ ⟨toFun (i + 1), toFun i, strictAntiOn hi.le hi (lt_add_one i)⟩

namespace JordanHolderFiltration

variable {μ : PayoffFunction ℒ S}

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
    cases F
    cases G
    dsimp only at h hlen
    subst h
    subst hlen
    rfl

@[simp] lemma toFun_eq_coe (F : μ.JordanHolderFiltration) : F.toFun = ⇑F := rfl

variable {F G : μ.JordanHolderFiltration} {m : ℕ}

/-- The first term is `⊤`. -/
@[simp] lemma apply_zero (F : μ.JordanHolderFiltration) : F 0 = ⊤ := F.head_eq_top

/-- The term at index `length` is `⊥`. -/
@[simp] lemma apply_length (F : μ.JordanHolderFiltration) : F F.length = ⊥ := F.length_eq_bot

/-- Below `F.length` the chain lies strictly above `⊥`. -/
lemma bot_lt_of_lt (h : m < F.length) : ⊥ < F m :=
  F.length_eq_bot ▸ F.strictAntiOn h.le (Set.mem_Iic.2 le_rfl) h

/-- Below `F.length` the chain has not yet reached `⊥`. -/
lemma ne_bot_of_lt (h : m < F.length) : F m ≠ ⊥ := (bot_lt_of_lt h).ne'

/-- The length is the least index at which the filtration reaches `⊥`. -/
lemma length_le_of_eq_bot (h : F m = ⊥) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_bot_of_lt hc h

/-- From `F.length` onwards, the chain is constantly `⊥`. -/
lemma eq_bot_of_length_le (h : F.length ≤ m) : F m = ⊥ :=
  le_bot_iff.1 <| F.length_eq_bot ▸ F.antitone h

/-- A term differs from `⊥` if and only if its index is less than the length. -/
lemma ne_bot_iff_lt_length : F m ≠ ⊥ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_bot_of_length_le hc), ne_bot_of_lt⟩

/-- Each term above `⊥` is strictly greater than its successor. -/
lemma succ_lt_of_ne_bot (h : F m ≠ ⊥) : F (m + 1) < F m := by
  have hm : m < F.length := ne_bot_iff_lt_length.1 h
  exact F.strictAntiOn hm.le hm (lt_add_one m)

/-- A Jordan–Hölder filtration of a nontrivial order has positive length. -/
lemma length_pos (F : μ.JordanHolderFiltration) : 0 < F.length :=
  Nat.pos_of_ne_zero fun h ↦
    top_ne_bot (α := ℒ) (F.head_eq_top.symm.trans (h ▸ F.length_eq_bot))

/-- Filtration terms strictly decrease up to `F.length`. -/
lemma apply_lt_apply {i j : ℕ} (hij : i < j) (hj : j ≤ F.length) : F j < F i :=
  F.strictAntiOn (hij.le.trans hj) hj hij

/-- Strictly after the start and up to `F.length`, the chain lies strictly below `⊤`. -/
lemma apply_lt_top (h0 : 0 < m) (hm : m ≤ F.length) : F m < ⊤ :=
  F.apply_zero ▸ apply_lt_apply h0 hm

/-- Each successive interval has the total payoff. -/
lemma step_payoff (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) :
    μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (lt_add_one i)⟩ = μ ⊤ :=
  F.step_payoff_eq i hi

/-- Replacing the upper endpoint of a step by a strictly intermediate point strictly
decreases its payoff. -/
lemma payoff_lt (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) {z : ℒ}
    (h' : F (i + 1) < z) (h'' : z < F i) :
    μ ⟨F (i + 1), z, h'⟩ < μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (lt_add_one i)⟩ :=
  F.payoff_lt_of_between i hi z h' h''

/-- Two Jordan–Hölder filtrations are equal if they agree at every index. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end JordanHolderFiltration

end JordanHolderFiltration

section JordanHolderRel

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- The relation between `x` and `y < x` for which the interval with endpoints `y` and `x`
has payoff `μ ⊤`, and replacing `x` by any strictly intermediate point gives a smaller payoff.

A finite series for this relation from `⊤` to `⊥` gives a Jordan–Hölder filtration. -/
def jordanHolderRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : y < x, μ ⟨y, x, h⟩ = μ ⊤ ∧
    ∀ z : ℒ, (h' : y < z) → z < x → μ ⟨y, z, h'⟩ < μ ⟨y, x, h⟩}

end JordanHolderRel

namespace JordanHolderFiltration

section SlopeLike

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable {μ : PayoffFunction ℒ S} [hsl : μ.IsSlopeLike]

/-- For a slope-like payoff function, the interval from `⊥` to any nonbottom filtration term
has the total payoff. -/
lemma payoff_bot_eq_top_payoff (F : μ.JordanHolderFiltration) (i : ℕ) (hi : i < F.length) :
    μ ⟨⊥, F i, F.bot_lt_of_lt hi⟩ = μ ⊤ := by
  induction i with
  | zero => simp only [apply_zero, StrictIntvl.mk_bot_top]
  | succ i ih =>
    refine (hsl.seesaw_total_eq_right_iff (F.bot_lt_of_lt hi)
      (F.apply_lt_top (Nat.zero_lt_succ i) hi.le)).1 ?_
    simp only [StrictIntvl.mk_bot_top]
    rw [← F.step_payoff (Nat.lt_of_succ_lt hi)]
    if htop : F i = ⊤ then
      simp only [htop]
    else
    refine (hsl.seesaw_left_eq_right_iff
      (F.apply_lt_apply (lt_add_one i) hi.le) (Ne.lt_top htop)).1 ?_
    specialize ih (Nat.lt_of_succ_lt hi)
    rw [← ((hsl.seesaw_total_eq_right_iff (F.bot_lt_of_lt (Nat.lt_of_succ_lt hi))
        (Ne.lt_top htop)).2 ih), F.step_payoff (Nat.lt_of_succ_lt hi)]
    rfl

end SlopeLike

end JordanHolderFiltration

end PayoffFunction

end HarderNarasimhan
