/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.SlopeLike
public import HarderNarasimhan.PayoffFunction.NashEquilibrium
public import Mathlib.Data.Rel

/-!
# Jordan–Hölder filtrations

This file defines the Jordan–Hölder filtrations of a payoff function
`μ : PayoffFunction ℒ S`: finite chains `⊤ = F 0 > F 1 > ⋯ > F F.length = ⊥` whose
successive steps all carry the total payoff `μ ⊤` and are *stable* in the sense that any
intermediate refinement strictly decreases the payoff.  Their existence is proved in
`HarderNarasimhan.JordanHolder.Exists`; the uniqueness of their length over a modular
lattice is proved in `HarderNarasimhan.JordanHolder.Length`.

The length of the chain is stored as a `length` field, but it carries no extra information:
it is provably the least index at which the chain reaches `⊥` (`length_le_of_eq_bot`), hence
it is determined by the chain itself; accordingly extensionality (`ext`) only requires the
underlying functions to agree.

The side conditions are `PayoffFunction.FiniteTotalPayoff`, the nondegeneracy hypothesis
that the total payoff is not already `⊤`, and `PayoffFunction.EventuallyTopDCC`, the chain
condition that every strictly descending chain has some step of payoff `⊤`.

Finally, `μ.jordanHolderRel` is the relation "`y < x` with total step payoff and strictly
smaller refinements", which lets a Jordan–Hölder filtration be repackaged as a `RelSeries`;
see `exists_relSeries_jordanHolderRel` in `HarderNarasimhan.JordanHolder.Exists`.

## Main definitions

* `PayoffFunction.FiniteTotalPayoff` : the total payoff `μ ⊤` is not `⊤`.
* `PayoffFunction.EventuallyTopDCC` : every strictly descending chain has a step of payoff
  `⊤`.
* `PayoffFunction.JordanHolderFiltration` : the structure packaging a Jordan–Hölder
  filtration for `μ`, applied to indices via the `FunLike` coercion.
* `PayoffFunction.jordanHolderRel` : the stable-step relation on `ℒ` used for the
  `RelSeries` packaging.

## Main results

* `JordanHolderFiltration.length_le_of_eq_bot`, `ne_bot_of_lt`, `eq_bot_of_length_le` :
  the `length` field is the least index at which the chain reaches `⊥`.
* `JordanHolderFiltration.ext` : two filtrations with the same underlying chain are equal.
* `JordanHolderFiltration.payoff_bot_eq_top_payoff` : below `length`, all initial segments
  `(⊥, F i)` carry the total payoff.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Classes

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A payoff function has *finite total payoff* when the payoff of the total interval
`(⊥, ⊤)` is not `⊤`.  This is the standard nondegeneracy hypothesis of the Jordan–Hölder
theory: it rules out the situation where every step of the construction collapses
immediately. -/
class FiniteTotalPayoff (μ : PayoffFunction ℒ S) : Prop where
  /-- The total payoff is not `⊤`. -/
  ne_top : μ ⊤ ≠ ⊤

/-- The *eventually-`⊤` descending chain condition* (`EventuallyTopDCC`): every strictly
descending chain has some step whose payoff is `⊤`.  The name refers to the existence of
such a step (`∃ N, μ (x (N + 1), x N) = ⊤`), not to `Filter.Eventually`.  This strengthens
`PayoffFunction.StrongDCC` and is the termination hypothesis making the Jordan–Hölder
construction reach `⊥` in finitely many steps. -/
class EventuallyTopDCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Some step of every strictly descending chain has payoff `⊤`. -/
  exists_eq_top : ∀ x : ℕ → ℒ, (hx : StrictAnti x) →
    ∃ N : ℕ, μ ⟨x (N + 1), x N, hx (lt_add_one N)⟩ = ⊤

variable {μ : PayoffFunction ℒ S}

/-- The eventually-`⊤` condition strengthens the strong descending chain condition: a step
of payoff `⊤` in particular dominates the corresponding initial payoff. -/
instance [h : μ.EventuallyTopDCC] : μ.StrongDCC where
  exists_le f saf := let ⟨N, hN⟩ := h.exists_eq_top f saf; ⟨N, hN ▸ le_top⟩

/-- The eventually-`⊤` condition is stable under restriction to a subinterval. -/
instance [h : μ.EventuallyTopDCC] {I : StrictIntvl ℒ} : (μ.restrict I).EventuallyTopDCC where
  exists_eq_top f saf := h.exists_eq_top (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ saf hn

end Classes

section RestrictBotFiniteTotalPayoff

variable [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- For a semistable slope-like payoff function, finite total payoff is inherited by the
restrictions to initial segments `(⊥, x)`: semistability forces `μ (⊥, x) ≤ μ ⊤ < ⊤`.  This
is used to apply the Jordan–Hölder theory to initial segments of a filtration. -/
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

/-- A **Jordan–Hölder filtration** for the payoff function `μ`: a finite chain
`⊤ = F 0 > F 1 > ⋯ > F F.length = ⊥`, extended constantly by `⊥` above `length`, whose
successive steps all carry the total payoff `μ ⊤` and are *stable*: refining a step through
any strictly intermediate point strictly decreases the payoff.

`length` is stored as data but carries no extra information: it is provably the *least*
index at which the chain reaches `⊥` (`length_le_of_eq_bot`), hence determined by `toFun`;
accordingly `ext` only asks for `toFun` to agree. -/
structure JordanHolderFiltration (μ : PayoffFunction ℒ S) where
  /-- The underlying chain; apply via the coercion, `F n`. -/
  toFun : ℕ → ℒ
  /-- The index at which the chain reaches `⊥`. -/
  length : ℕ
  /-- The chain is antitone (constantly `⊥` above `length`). -/
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
  /-- Refining a step through a strictly intermediate point strictly decreases the payoff. -/
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

/-- The chain starts at `⊤`, stated for the coercion. -/
@[simp] lemma apply_zero (F : μ.JordanHolderFiltration) : F 0 = ⊤ := F.head_eq_top

/-- The chain reaches `⊥` at index `length`, stated for the coercion. -/
@[simp] lemma apply_length (F : μ.JordanHolderFiltration) : F F.length = ⊥ := F.length_eq_bot

/-- Below `F.length` the chain lies strictly above `⊥`. -/
lemma bot_lt_of_lt (h : m < F.length) : ⊥ < F m :=
  F.length_eq_bot ▸ F.strictAntiOn h.le (Set.mem_Iic.2 le_rfl) h

/-- Below `F.length` the chain has not yet reached `⊥`. -/
lemma ne_bot_of_lt (h : m < F.length) : F m ≠ ⊥ := (bot_lt_of_lt h).ne'

/-- Minimality of the `length` field: it is the least index at which the chain reaches
`⊥`.  In particular `length` is determined by the underlying chain. -/
lemma length_le_of_eq_bot (h : F m = ⊥) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_bot_of_lt hc h

/-- Above `F.length` the chain is constantly `⊥`. -/
lemma eq_bot_of_length_le (h : F.length ≤ m) : F m = ⊥ :=
  le_bot_iff.1 <| F.length_eq_bot ▸ F.antitone h

/-- The chain has reached `⊥` at an index iff the index is at least `F.length`. -/
lemma ne_bot_iff_lt_length : F m ≠ ⊥ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_bot_of_length_le hc), ne_bot_of_lt⟩

/-- One-step strict decrease of the chain before it reaches `⊥`. -/
lemma succ_lt_of_ne_bot (h : F m ≠ ⊥) : F (m + 1) < F m := by
  have hm : m < F.length := ne_bot_iff_lt_length.1 h
  exact F.strictAntiOn hm.le hm (lt_add_one m)

/-- A Jordan–Hölder filtration has positive length, since it starts at `⊤` and ends at
`⊥`. -/
lemma length_pos (F : μ.JordanHolderFiltration) : 0 < F.length :=
  Nat.pos_of_ne_zero fun h ↦
    top_ne_bot (α := ℒ) (F.head_eq_top.symm.trans (h ▸ F.length_eq_bot))

/-- Strict decrease of the chain up to `F.length`, stated for the coercion. -/
lemma apply_lt_apply {i j : ℕ} (hij : i < j) (hj : j ≤ F.length) : F j < F i :=
  F.strictAntiOn (hij.le.trans hj) hj hij

/-- Strictly after the start and up to `F.length`, the chain lies strictly below `⊤`. -/
lemma apply_lt_top (h0 : 0 < m) (hm : m ≤ F.length) : F m < ⊤ :=
  F.apply_zero ▸ apply_lt_apply h0 hm

/-- The step condition `step_payoff_eq`, stated for the coercion. -/
lemma step_payoff (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) :
    μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (lt_add_one i)⟩ = μ ⊤ :=
  F.step_payoff_eq i hi

/-- The stability condition `payoff_lt_of_between`, stated for the coercion. -/
lemma payoff_lt (F : μ.JordanHolderFiltration) {i : ℕ} (hi : i < F.length) {z : ℒ}
    (h' : F (i + 1) < z) (h'' : z < F i) :
    μ ⟨F (i + 1), z, h'⟩ < μ ⟨F (i + 1), F i, F.strictAntiOn hi.le hi (lt_add_one i)⟩ :=
  F.payoff_lt_of_between i hi z h' h''

/-- Two Jordan–Hölder filtrations with the same underlying chain are equal: the `length`
field is determined by the chain (`length_le_of_eq_bot`) and the remaining fields are
proofs. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end JordanHolderFiltration

end JordanHolderFiltration

section JordanHolderRel

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- The step relation of the Jordan–Hölder theory: `(x, y)` is related when `y < x`, the
payoff of `(y, x)` is the total payoff `μ ⊤`, and any strictly intermediate refinement has
strictly smaller payoff.  A Jordan–Hölder filtration is precisely a `RelSeries` for this
relation from `⊤` to `⊥`; see `exists_relSeries_jordanHolderRel`. -/
def jordanHolderRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : y < x, μ ⟨y, x, h⟩ = μ ⊤ ∧
    ∀ z : ℒ, (h' : y < z) → z < x → μ ⟨y, z, h'⟩ < μ ⟨y, x, h⟩}

end JordanHolderRel

namespace JordanHolderFiltration

section SlopeLike

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable {μ : PayoffFunction ℒ S} [hsl : μ.IsSlopeLike]

/-- Below `F.length`, every initial segment `(⊥, F i)` of a Jordan–Hölder filtration
carries the total payoff `μ ⊤`: the seesaw property propagates the total payoff of the
steps down the chain. -/
lemma payoff_bot_eq_top_payoff (F : μ.JordanHolderFiltration) (i : ℕ) (hi : i < F.length) :
    μ ⟨⊥, F i, F.bot_lt_of_lt hi⟩ = μ ⊤ := by
  induction i with
  | zero => simp only [apply_zero, StrictIntvl.mk_bot_top]
  | succ i ih =>
    refine (hsl.seesaw_total_eq_right_iff (F.bot_lt_of_lt hi)
      (F.apply_lt_top (Nat.zero_lt_succ i) (le_of_lt hi))).1 ?_
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
