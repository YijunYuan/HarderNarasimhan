/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.GameValue
public import HarderNarasimhan.PayoffFunction.Semistable.Defs
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE

/-!
# Nash equilibria of the Harder–Narasimhan Games

The Harder–Narasimhan Games associated to `μ` *has a Nash equilibrium* when its two values
coincide: `μ.A ⊤ = μ.B ⊤` (`HasNashEquilibrium`).  This file relates that condition to the
global extremal values `μ.min ⊤` and `μ.max ⊤` and, over a linear order, to semistability.

## Main results

* `B_top_le_A_top_iff`, `hasNashEquilibrium_iff_min_le`, `hasNashEquilibrium_iff_le_max` :
  unfolded reformulations of the equilibrium condition.
* `B_top_le_A_top_of_min_eq_max`, `min_top_eq_max_top_of_B_top_le_A_top` : the equivalence
  between the inequality `μ.B ⊤ ≤ μ.A ⊤` and the coincidence of the global extremal values.
* `max_top_eq_apply_iff`, `min_top_eq_apply_iff` : for a slope-like payoff the endpoint
  equalities `μ.max ⊤ = μ ⊤`, `μ.min ⊤ = μ ⊤` and `μ.min ⊤ = μ.max ⊤` are equivalent.
* `min_top_eq_max_top_iff_hasNashEquilibrium`, `nashEquilibrium_tfae` : under both chain
  conditions the above are further equivalent to `HasNashEquilibrium`.
* `IsSemistable.B_top_le_A_top`, `IsSemistable.hasNashEquilibrium`,
  `isSemistable_of_hasNashEquilibrium` : the equivalence between semistability and Nash
  equilibrium over a complete linear order.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable {μ : PayoffFunction ℒ S}

/-- The Harder–Narasimhan Games of `μ` *has a Nash equilibrium* when the first-player and
second-player values coincide: `μ.A ⊤ = μ.B ⊤`, i.e. the minimax and maximin values agree
and the game has a value. -/
class HasNashEquilibrium (μ : PayoffFunction ℒ S) : Prop where
  /-- The two game values coincide. -/
  eq : μ.A ⊤ = μ.B ⊤

/-- The inequality `μ.B ⊤ ≤ μ.A ⊤`, unfolded as a family of comparisons between
bottom-anchored minima and top-anchored maxima. -/
theorem B_top_le_A_top_iff :
    μ.B ⊤ ≤ μ.A ⊤ ↔
      ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) →
        μ.min ⟨⊥, y, hy⟩ ≤ μ.max ⟨x, ⊤, lt_top_iff_ne_top.2 hx⟩ := by
  constructor
  · intro h x hx y hy
    calc
      μ.min ⟨⊥, y, hy⟩ ≤ μ.B ⊤ := le_B (I := ⊤) ⟨hy, le_top⟩
      _ ≤ μ.A ⊤ := h
      _ ≤ μ.max ⟨x, ⊤, lt_top_iff_ne_top.2 hx⟩ :=
        A_le (I := ⊤) ⟨bot_le, lt_top_iff_ne_top.2 hx⟩
  · exact fun h ↦ B_le fun y hy ↦ le_A fun x hx ↦ h x hx.2.ne y hy.1

/-- Under the hypotheses computing player A's value, the game has a Nash equilibrium iff no
proper initial segment has a smaller minimum than the total interval. -/
theorem hasNashEquilibrium_iff_min_le [μ.WeakACC] [μ.WeakSlopeLikeAtTop] :
    μ.HasNashEquilibrium ↔
      ∀ y : ℒ, (hy : y ≠ ⊥) → μ.min ⟨⊥, y, bot_lt_iff_ne_bot.2 hy⟩ ≤ μ.min ⊤ := by
  constructor
  · intro h y hy
    calc
      μ.min ⟨⊥, y, bot_lt_iff_ne_bot.2 hy⟩ ≤ μ.B ⊤ :=
        le_B (I := ⊤) ⟨bot_lt_iff_ne_bot.2 hy, le_top⟩
      _ = μ.A ⊤ := h.eq.symm
      _ = μ.min ⊤ := A_top_eq_min_top
  · intro h
    refine ⟨?_⟩
    rw [A_top_eq_min_top]
    exact eq_of_le_of_ge (le_iSup₂_of_le ⊤ ⟨bot_lt_top, le_rfl⟩ le_rfl)
      (iSup₂_le fun b hb ↦ h b hb.1.ne')

/-- Under the hypotheses computing player B's value, the game has a Nash equilibrium iff no
proper final segment has a larger maximum than the total interval. -/
theorem hasNashEquilibrium_iff_le_max [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] :
    μ.HasNashEquilibrium ↔
      ∀ y : ℒ, (hy : y ≠ ⊤) → μ.max ⊤ ≤ μ.max ⟨y, ⊤, lt_top_iff_ne_top.2 hy⟩ := by
  constructor
  · intro h y hy
    calc
      μ.max ⊤ = μ.B ⊤ := B_top_eq_max_top.symm
      _ = μ.A ⊤ := h.eq.symm
      _ ≤ μ.max ⟨y, ⊤, lt_top_iff_ne_top.2 hy⟩ :=
        A_le (I := ⊤) ⟨bot_le, lt_top_iff_ne_top.2 hy⟩
  · intro h
    refine ⟨?_⟩
    rw [B_top_eq_max_top (μ := μ)]
    exact eq_of_le_of_ge (iInf₂_le ⊥ ⟨le_rfl, bot_lt_top⟩)
      (le_iInf₂ fun b hb ↦ h b hb.2.ne)

/-- If the global extremal values coincide, then `μ.B ⊤ ≤ μ.A ⊤`. -/
theorem B_top_le_A_top_of_min_eq_max (h : μ.min ⊤ = μ.max ⊤) : μ.B ⊤ ≤ μ.A ⊤ := by
  calc
    μ.B ⊤ ≤ μ.max ⊤ := B_le fun b hb ↦ min_le_apply.trans (le_max hb)
    _ = μ.min ⊤ := h.symm
    _ ≤ μ.A ⊤ := le_A fun b hb ↦ (min_le hb).trans apply_le_max

/-- Conversely, under the hypotheses computing both game values, `μ.B ⊤ ≤ μ.A ⊤` forces the
global extremal values to coincide. -/
theorem min_top_eq_max_top_of_B_top_le_A_top [μ.WeakACC] [μ.WeakSlopeLikeAtTop]
    [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] (h : μ.B ⊤ ≤ μ.A ⊤) : μ.min ⊤ = μ.max ⊤ :=
  eq_of_le_of_ge (le_trans min_le_apply apply_le_max) <|
    B_top_eq_max_top (μ := μ) ▸ A_top_eq_min_top (μ := μ) ▸ h

private lemma min_eq_max_of_max_eq
    (h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
      μ ⊤ ≤ μ ⟨x, ⊤, lt_top_iff_ne_top.2 hx.2⟩) :
    μ.max ⊤ = μ ⊤ → μ.min ⊤ = μ.max ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge min_le_apply (le_iInf₂ fun b hb ↦ ?_)
  by_cases hbot : b = ⊥
  · subst hbot
    exact le_rfl
  refine (h b ⟨hbot, hb.2.ne⟩).resolve_left (not_not.2 ?_)
  exact h' ▸ le_iSup₂_of_le b ⟨bot_lt_iff_ne_bot.2 hbot, le_top⟩ le_rfl

private lemma max_eq_min_of_min_eq
    (h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
      ¬ μ ⊤ ≤ μ ⟨x, ⊤, lt_top_iff_ne_top.2 hx.2⟩) :
    μ.min ⊤ = μ ⊤ → μ.max ⊤ = μ.min ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge (iSup₂_le fun b hb ↦ ?_) apply_le_max
  by_cases htop : b = ⊤
  · subst htop
    exact le_rfl
  refine (h b ⟨hb.1.ne', htop⟩).resolve_right (not_not.2 ?_)
  exact h' ▸ iInf₂_le b ⟨bot_le, lt_top_iff_ne_top.2 htop⟩

section SlopeLike

variable [hμ : μ.IsSlopeLike]

/-- For a slope-like payoff function, `μ.max ⊤ = μ ⊤` says exactly that the two global
extremal values coincide.  Together with `min_top_eq_apply_iff` this makes the two endpoint
equalities `μ.max ⊤ = μ ⊤` and `μ.min ⊤ = μ ⊤` interchangeable. -/
theorem max_top_eq_apply_iff : μ.max ⊤ = μ ⊤ ↔ μ.min ⊤ = μ.max ⊤ := by
  constructor
  · exact min_eq_max_of_max_eq fun x hx ↦
      ((hμ.slopelike ⊥ x ⊤
        ⟨bot_lt_iff_ne_bot.2 hx.1, lt_top_iff_ne_top.2 hx.2⟩).2.2.1).imp_left not_le_of_gt
  · intro h
    exact le_antisymm (h.symm.trans_le min_le_apply) apply_le_max

/-- For a slope-like payoff function, `μ.min ⊤ = μ ⊤` says exactly that the two global
extremal values coincide. -/
theorem min_top_eq_apply_iff : μ.min ⊤ = μ ⊤ ↔ μ.min ⊤ = μ.max ⊤ := by
  constructor
  · exact fun h ↦ (max_eq_min_of_min_eq (fun x hx ↦
      ((hμ.slopelike ⊥ x ⊤
        ⟨bot_lt_iff_ne_bot.2 hx.1, lt_top_iff_ne_top.2 hx.2⟩).1).imp_right not_le_of_gt) h).symm
  · intro h
    exact le_antisymm min_le_apply (apply_le_max.trans_eq h.symm)

/-- For a slope-like payoff function satisfying both chain conditions, the game has a Nash
equilibrium iff the two global extremal values coincide.  This is the key bridge between the
extremal operations and the game values. -/
theorem min_top_eq_max_top_iff_hasNashEquilibrium [h₁ : μ.WeakACC] [h₂ : μ.StrongDCC] :
    μ.min ⊤ = μ.max ⊤ ↔ μ.HasNashEquilibrium := by
  have hwsl : μ.WeakSlopeLikeAtTop :=
    ⟨fun z hz ↦ (hμ.slopelike z.left z.right ⊤ ⟨z.lt, hz⟩).1.imp_right le_of_lt⟩
  have hwsl' : μ.WeakSlopeLikeAtBot :=
    ⟨fun z hz ↦ ((hμ.slopelike ⊥ z.left z.right ⟨hz, z.lt⟩).2.2.1.imp_left le_of_lt).symm⟩
  exact ⟨fun h ↦ ⟨eq_of_le_of_ge A_top_le_B_top <| B_top_le_A_top_of_min_eq_max h⟩,
    fun h ↦ min_top_eq_max_top_of_B_top_le_A_top h.eq.symm.le⟩

/-- The four equivalent formulations of Nash equilibrium for a slope-like payoff function
satisfying both chain conditions.  This `TFAE` is a summary statement; the individual
equivalences `max_top_eq_apply_iff`, `min_top_eq_apply_iff` and
`min_top_eq_max_top_iff_hasNashEquilibrium` are the working API. -/
theorem nashEquilibrium_tfae [μ.WeakACC] [μ.StrongDCC] :
    List.TFAE [μ.max ⊤ = μ ⊤, μ.min ⊤ = μ ⊤, μ.min ⊤ = μ.max ⊤, μ.HasNashEquilibrium] := by
  tfae_have 1 ↔ 3 := max_top_eq_apply_iff
  tfae_have 2 ↔ 3 := min_top_eq_apply_iff
  tfae_have 3 ↔ 4 := min_top_eq_max_top_iff_hasNashEquilibrium
  tfae_finish

end SlopeLike

section Semistable

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]

/-- Over a complete linear order, semistability implies `μ.B ⊤ ≤ μ.A ⊤`. -/
theorem IsSemistable.B_top_le_A_top {S : Type*} [CompleteLinearOrder S]
    {μ : PayoffFunction ℒ S} (hμ : μ.IsSemistable) : μ.B ⊤ ≤ μ.A ⊤ := by
  rw [isSemistable_iff_isBreakpoint_top] at hμ
  refine B_le fun x hx ↦ ?_
  calc
    μ.min ⟨⊥, x, hx.1⟩ ≤ μ.A ⟨⊥, x, hx.1⟩ :=
      le_A fun y hy ↦ (min_le hy).trans apply_le_max
    _ ≤ μ.A ⊤ := le_of_not_gt (hμ.not_lt x (StrictIntvl.mem_top x) hx.1.ne)

/-- Over a complete linear order, a semistable payoff function has a Nash equilibrium under
the hypotheses computing player A's value. -/
theorem IsSemistable.hasNashEquilibrium {S : Type*} [CompleteLinearOrder S]
    {μ : PayoffFunction ℒ S} (hμ : μ.IsSemistable) [μ.WeakACC] [μ.WeakSlopeLikeAtTop] :
    μ.HasNashEquilibrium :=
  ⟨eq_of_le_of_ge A_top_le_B_top hμ.B_top_le_A_top⟩

/-- A Nash equilibrium forces semistability, provided every bottom-anchored restriction
satisfies the hypotheses computing player A's value. -/
theorem isSemistable_of_hasNashEquilibrium {S : Type*} [CompleteLattice S]
    {μ : PayoffFunction ℒ S}
    (h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) → (μ.restrict ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩).WeakACC)
    (h₂ : ∀ x : ℒ, (hx : x ≠ ⊥) →
      (μ.restrict ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩).WeakSlopeLikeAtTop)
    (h : μ.HasNashEquilibrium) : μ.IsSemistable := by
  refine ⟨fun x hx ↦ not_lt_of_ge ?_⟩
  -- Compute the value on the initial segment, then compare it with the global game value.
  calc
    μ.A ⟨⊥, x, hx⟩ = μ.min ⟨⊥, x, hx⟩ := by
      simpa only [A_restrict_apply, min_restrict_apply, StrictIntvl.ofSub_top] using
        A_top_eq_min_top (μ := μ.restrict ⟨⊥, x, hx⟩)
          (h₁ := h₁ x hx.ne') (h₂ := h₂ x hx.ne')
    _ ≤ μ.B ⊤ := le_B (I := ⊤) ⟨hx, le_top⟩
    _ = μ.A ⊤ := h.eq.symm

end Semistable

end PayoffFunction

end HarderNarasimhan
