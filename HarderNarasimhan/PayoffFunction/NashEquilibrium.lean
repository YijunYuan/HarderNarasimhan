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
    exact le_trans (le_iSup₂_of_le y ⟨hy, le_top⟩ le_rfl) <|
      h.trans (iInf₂_le x ⟨bot_le, lt_top_iff_ne_top.2 hx⟩)
  · exact fun h ↦ iSup₂_le fun y hy ↦ le_iInf₂ fun x hx ↦ h x hx.2.ne y hy.1

/-- Under the hypotheses computing player A's value, the game has a Nash equilibrium iff no
proper initial segment has a smaller minimum than the total interval. -/
theorem hasNashEquilibrium_iff_min_le [μ.WeakACC] [μ.WeakSlopeLikeAtTop] :
    μ.HasNashEquilibrium ↔
      ∀ y : ℒ, (hy : y ≠ ⊥) → μ.min ⟨⊥, y, bot_lt_iff_ne_bot.2 hy⟩ ≤ μ.min ⊤ := by
  constructor
  · intro h y hy
    have h := h.eq
    rw [A_top_eq_min_top] at h
    rw [h]
    exact le_iSup₂_of_le y ⟨bot_lt_iff_ne_bot.2 hy, le_top⟩ le_rfl
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
    have h := h.eq
    rw [B_top_eq_max_top (μ := μ)] at h
    rw [← h]
    exact iInf₂_le y ⟨bot_le, lt_top_iff_ne_top.2 hy⟩
  · intro h
    refine ⟨?_⟩
    rw [B_top_eq_max_top (μ := μ)]
    exact eq_of_le_of_ge (iInf₂_le ⊥ ⟨le_rfl, bot_lt_top⟩)
      (le_iInf₂ fun b hb ↦ h b hb.2.ne)

/-- If the global extremal values coincide, then `μ.B ⊤ ≤ μ.A ⊤`. -/
theorem B_top_le_A_top_of_min_eq_max (h : μ.min ⊤ = μ.max ⊤) : μ.B ⊤ ≤ μ.A ⊤ := by
  have h₁ : μ.B ⊤ ≤ μ.max ⊤ :=
    iSup₂_le fun b hb ↦ le_trans (min_le_apply (I := ⟨⊥, b, hb.1⟩)) <|
      le_iSup₂_of_le b hb le_rfl
  have h₂ : μ.min ⊤ ≤ μ.A ⊤ :=
    le_iInf₂ fun b hb ↦ le_trans (iInf₂_le b hb) (apply_le_max (I := ⟨b, ⊤, hb.2⟩))
  exact h₁.trans (h ▸ h₂)

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
    have hb : μ.min ⊤ ≤ μ ⊤ ∧ μ ⊤ ≤ μ.max ⊤ := ⟨min_le_apply, apply_le_max⟩
    exact (h ▸ hb).elim eq_of_le_of_ge

/-- For a slope-like payoff function, `μ.min ⊤ = μ ⊤` says exactly that the two global
extremal values coincide. -/
theorem min_top_eq_apply_iff : μ.min ⊤ = μ ⊤ ↔ μ.min ⊤ = μ.max ⊤ := by
  constructor
  · exact fun h ↦ (max_eq_min_of_min_eq (fun x hx ↦
      ((hμ.slopelike ⊥ x ⊤
        ⟨bot_lt_iff_ne_bot.2 hx.1, lt_top_iff_ne_top.2 hx.2⟩).1).imp_right not_le_of_gt) h).symm
  · intro h
    have hb : μ.min ⊤ ≤ μ ⊤ ∧ μ ⊤ ≤ μ.max ⊤ := ⟨min_le_apply, apply_le_max⟩
    exact (h.symm ▸ hb).elim eq_of_le_of_ge

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
  have hstep : ∀ (x : ℒ) (hx : ⊥ < x), μ.A ⟨⊥, x, hx⟩ ≤ μ.A ⊤ := fun x hx ↦
    le_of_not_gt <| hμ.not_lt x (StrictIntvl.mem_top x) hx.ne
  refine iSup₂_le fun x hx ↦ le_trans ?_ (hstep x hx.1)
  exact le_iInf₂ fun y hy ↦ iInf₂_le_of_le y hy (apply_le_max (I := ⟨y, x, hy.2⟩))

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
  have h := h.eq
  have key : ∀ (x : ℒ) (hx : ⊥ < x), μ.A ⟨⊥, x, hx⟩ = μ.min ⟨⊥, x, hx⟩ := by
    intro x hx
    have := A_top_eq_min_top (μ := μ.restrict ⟨⊥, x, hx⟩)
      (h₁ := h₁ x hx.ne') (h₂ := h₂ x hx.ne')
    rwa [A_restrict_apply, min_restrict_apply, StrictIntvl.ofSub_top] at this
  have hB : (⨆ (x : ℒ) (hx : ⊥ < x), μ.A ⟨⊥, x, hx⟩) = μ.B ⊤ :=
    le_antisymm (iSup₂_le fun x hx ↦ le_iSup₂_of_le x ⟨hx, le_top⟩ (key x hx).le)
      (iSup₂_le fun x hx ↦ le_iSup₂_of_le x hx.1 (key x hx.1).ge)
  have hle : ∀ x : ℒ, (hx : x ≠ ⊥) → μ.A ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩ ≤ μ.A ⊤ := by
    rw [← h] at hB
    intro x hx
    rw [← hB]
    exact le_iSup₂_of_le x (bot_lt_iff_ne_bot.2 hx) le_rfl
  exact ⟨fun x hx ↦ (hle x hx.ne').not_gt⟩

end Semistable

end PayoffFunction

end HarderNarasimhan
