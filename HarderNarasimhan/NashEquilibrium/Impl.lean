/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.NashEquilibrium.Defs
import HarderNarasimhan.PayoffFunction.GameValue
import HarderNarasimhan.PayoffFunction.GameValue
import HarderNarasimhan.PayoffFunction.SlopeLike
import HarderNarasimhan.PayoffFunction.Semistable.Breakpoints
import HarderNarasimhan.Interval
import Mathlib.Tactic.TFAE
import Mathlib.Data.List.TFAE

/-!
  # Nash equilibrium: internal implementation lemmas

  This file contains the internal (non-export) proofs for the Nash-equilibrium layer
  of the development. The key technical theme is to relate the global extremal values
  `μmin μ ⊤` and `μmax μ ⊤` to the “best responses” quantities `μAstar μ`
  and `μBstar μ`, and to package the resulting equivalences as TFAE chains.

  The statements are named after the corresponding remarks/propositions/theorem in the
  accompanying text (e.g. `rmk4d10₀`, `prop4d16₂`, `thm4d21`).

  API note: this file is internal (lemmas live in `HarderNarasimhan.impl`). For a stable
  interface, prefer importing `HarderNarasimhan.NashEquilibrium.Results`.
-/

namespace HarderNarasimhan

namespace impl

/- Transitional bridges restating the game-value computations of
`HarderNarasimhan.PayoffFunction.GameValue` in the `μAstar`/`μBstar` spelling still used in
this file; they disappear when this file is rewritten. -/

private lemma prop4d1₁ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
    (S : Type*) [CompleteLattice S] (μ : PayoffFunction ℒ S)
    [h₁ : μ.WeakACC] [h₂ : μ.WeakSlopeLikeAtTop] :
    μAstar μ = μmin μ ⊤ :=
  PayoffFunction.A_top_eq_min_top

private lemma prop4d1₂ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
    (S : Type*) [CompleteLattice S] (μ : PayoffFunction ℒ S)
    [h₁ : μ.WeakACC] [h₂ : μ.WeakSlopeLikeAtTop] :
    μAstar μ ≤ μBstar μ :=
  PayoffFunction.A_top_le_B_top

private lemma prop4d3₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
    {S : Type*} [CompleteLattice S] (μ : PayoffFunction ℒ S)
    [h₁ : μ.StrongDCC] [h₂ : μ.WeakSlopeLikeAtBot] :
    μBstar μ = μmax μ ⊤ :=
  PayoffFunction.B_top_eq_max_top

private lemma prop4d3₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
    {S : Type*} [CompleteLattice S] (μ : PayoffFunction ℒ S)
    [h₁ : μ.StrongDCC] [h₂ : μ.WeakSlopeLikeAtBot] :
    μAstar μ ≤ μBstar μ :=
  PayoffFunction.A_top_le_B_top_of_strongDCC

/-- `rmk4d10₀` records the basic bounds: for any interval `I`, `μmin μ I ≤ μ I ≤ μmax μ I`.
  This is a direct consequence of the defining bounded-infimum/supremum characterisations.
-/
lemma rmk4d10₀ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) :
∀ I : StrictIntvl ℒ, μmin μ I ≤ μ I ∧ μ I ≤ μmax μ I :=
  fun I ↦ ⟨iInf₂_le I.left ⟨le_rfl, I.lt⟩,
    le_iSup₂_of_le I.right ⟨I.lt, le_rfl⟩ le_rfl⟩



/-- `rmk4d10₁` rewrites the inequality `μBstar μ ≤ μAstar μ` as an explicit family of
  inequalities comparing the extremal values on bottom- and top-anchored intervals.
  This is a convenient “unfolded” form for later arguments.
-/
lemma rmk4d10₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) :
μBstar μ ≤ μAstar μ ↔
  ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) →
    μmin μ ⟨⊥, y,hy⟩ ≤ μmax μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx⟩ := by
  constructor
  · intro h x hx y hy
    exact le_trans (le_iSup₂_of_le y ⟨hy, le_top⟩ le_rfl) <|
      h.trans (iInf₂_le x ⟨bot_le, lt_top_iff_ne_top.2 hx⟩)
  · exact fun h ↦ iSup₂_le fun y hy ↦ le_iInf₂ fun x hx ↦ h x hx.2.ne y hy.1



/-- `rmk4d10₂` specialises Nash equilibrium to the case where we have a weak ascending
  chain condition together with the first weak slope-like axiom.

  Under these hypotheses, Nash equilibrium is equivalent to a single family of
  inequalities comparing `μmin` on bottom-anchored intervals with `μmin` on `⊤`.
-/
lemma rmk4d10₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h₁ : μ.WeakACC) (h₂ : μ.WeakSlopeLikeAtTop) :
NashEquilibrium μ ↔
  ∀ y : ℒ, (hy : y ≠ ⊥) → μmin μ ⟨⊥, y,bot_lt_iff_ne_bot.2 hy⟩ ≤ μmin μ ⊤ := by
  constructor
  · intro h y hy
    replace h := h.nash_eq
    rw [impl.prop4d1₁ ℒ S μ (h₁ := h₁) (h₂ := h₂)] at h
    rw [h]
    exact le_iSup₂_of_le y ⟨bot_lt_iff_ne_bot.2 hy, le_top⟩ le_rfl
  · intro h
    refine {nash_eq := ?_}
    rw [impl.prop4d1₁ ℒ S μ (h₁ := h₁) (h₂ := h₂)]
    exact eq_of_le_of_ge (le_iSup₂_of_le ⊤ ⟨bot_lt_top, le_rfl⟩ le_rfl)
      (iSup₂_le fun b hb ↦ h b hb.1.ne')



/-- `rmk4d10₃` is the dual counterpart of `rmk4d10₂`.

  Assuming a strong descending chain condition and the second weak slope-like axiom,
  Nash equilibrium is equivalent to a family of inequalities comparing `μmax` on
  `⊤` with `μmax` on top-anchored intervals.
-/
lemma rmk4d10₃ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h₁ : μ.StrongDCC) (h₂ : μ.WeakSlopeLikeAtBot) :
NashEquilibrium μ ↔
  ∀ y : ℒ, (hy : y ≠ ⊤) → μmax μ ⊤ ≤ μmax μ ⟨y, ⊤,lt_top_iff_ne_top.2 hy⟩ := by
  constructor
  · intro h y hy
    replace h := h.nash_eq
    rw [impl.prop4d3₁ μ (h₁ := h₁) (h₂ := h₂)] at h
    rw [← h]
    exact iInf₂_le y ⟨bot_le, lt_top_iff_ne_top.2 hy⟩
  · intro h
    refine {nash_eq := ?_}
    rw [impl.prop4d3₁ μ (h₁ := h₁) (h₂ := h₂)]
    exact eq_of_le_of_ge (iInf₂_le ⊥ ⟨le_rfl, bot_lt_top⟩)
      (le_iInf₂ fun b hb ↦ h b hb.2.ne)



/-- `prop4d11₁` shows that if the global extremal values on `⊤` coincide, then
  the best-response inequality `μBstar μ ≤ μAstar μ` holds.
-/
lemma prop4d11₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) :
μmin μ ⊤ = μmax μ ⊤ → μBstar μ ≤ μAstar μ := by
  have h₁ : μBstar μ ≤ μmax μ ⊤ :=
    iSup₂_le fun b hb ↦ le_trans (rmk4d10₀ μ ⟨⊥, b, hb.1⟩).1 <|
      le_iSup₂_of_le b hb le_rfl
  have h₂ : μmin μ ⊤ ≤ μAstar μ :=
    le_iInf₂ fun b hb ↦ le_trans (iInf₂_le b hb) (rmk4d10₀ μ ⟨b, ⊤, hb.2⟩).2
  exact fun h ↦ h₁.trans (h ▸ h₂)



/-- `prop4d11₂` is a converse direction: under the weak chain/slope hypotheses on both
  sides, the inequality `μBstar μ ≤ μAstar μ` forces equality of the global extremal
  values `μmin μ ⊤` and `μmax μ ⊤`.
-/
lemma prop4d11₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h₁ : μ.WeakACC) (h₂ : μ.WeakSlopeLikeAtTop)
(h₁' : μ.StrongDCC) (h₂' : μ.WeakSlopeLikeAtBot) :
μBstar μ ≤ μAstar μ → μmin μ ⊤ = μmax μ ⊤ :=
  fun h ↦ eq_of_le_of_ge (le_trans (rmk4d10₀ μ ⊤).1 (rmk4d10₀ μ ⊤).2) <|
    (impl.prop4d3₁ μ (h₁ := h₁') (h₂ := h₂')) ▸
      (impl.prop4d1₁ ℒ S μ (h₁ := h₁) (h₂ := h₂)) ▸ h



/-- `prop4d12` derives the equality `μmin μ ⊤ = μmax μ ⊤` from the
  stronger equality `μmax μ ⊤ = μ ⊤`, provided a pointwise dichotomy
  that rules out “intermediate” points simultaneously satisfying both comparisons.
-/
lemma prop4d12 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩) :
μmax μ ⊤ = μ ⊤ → μmin μ ⊤ = μmax μ ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge (rmk4d10₀ μ ⊤).1
    (le_iInf₂ fun b hb ↦ ?_)
  by_cases hbot : b = ⊥
  · subst hbot
    exact le_rfl
  refine Or.resolve_left (h b ⟨hbot, hb.2.ne⟩) (not_not.2 ?_)
  exact h' ▸ le_iSup₂_of_le b ⟨bot_lt_iff_ne_bot.2 hbot, le_top⟩ le_rfl



/-- `rmk4d13` shows that the dichotomy assumption used in `prop4d12` follows from a
  genuine `μ.IsSlopeLike` structure.
-/
lemma rmk4d13 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSlopeLike) :
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩ :=
  fun x hx ↦ ((hμ.slopelike ⊥ x ⊤
    ⟨bot_lt_iff_ne_bot.2 hx.1,lt_top_iff_ne_top.2 hx.2⟩).2.2.1).imp_left not_le_of_gt



/-- `prop4d14` is the dual analogue of `prop4d12`: starting from `μmin μ ⊤ = μ ⊤`
  and a suitable dichotomy, it deduces `μmax μ ⊤ = μmin μ ⊤`.
-/
lemma prop4d14 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  ¬ μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩) :
μmin μ ⊤ = μ ⊤ → μmax μ ⊤ = μmin μ ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge
    (iSup₂_le fun b hb ↦ ?_) (rmk4d10₀ μ ⊤).2
  by_cases htop : b = ⊤
  · subst htop
    exact le_rfl
  refine Or.resolve_right (h b ⟨hb.1.ne', htop⟩) (not_not.2 ?_)
  exact h' ▸ iInf₂_le b ⟨bot_le, lt_top_iff_ne_top.2 htop⟩



/-- `rmk4d15` shows that the dichotomy assumption used in `prop4d14` also follows from
  a `μ.IsSlopeLike` structure.
-/
lemma rmk4d15 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSlopeLike) :
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  ¬ μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩ :=
  fun x hx ↦ ((hμ.slopelike ⊥ x ⊤
    ⟨bot_lt_iff_ne_bot.2 hx.1,lt_top_iff_ne_top.2 hx.2⟩).1).imp_right not_le_of_gt



/-- `prop4d16₁` bundles three “endpoint equalities” into a `List.TFAE` statement.
  It uses `prop4d12/prop4d14` (with `rmk4d13/rmk4d15`) to connect them, and the
  elementary bounds from `rmk4d10₀` for the remaining implications.
-/
lemma prop4d16₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSlopeLike) :
List.TFAE [
  μmax μ ⊤ = μ ⊤, μmin μ ⊤ = μ ⊤, μmin μ ⊤ = μmax μ ⊤
  ] := by
  tfae_have 1 → 3 := prop4d12 μ (rmk4d13 μ hμ)
  tfae_have 2 → 3 := fun h ↦ (prop4d14 μ (rmk4d15 μ hμ) h).symm
  tfae_have 3 → 1 := fun h ↦ (h ▸ rmk4d10₀ μ ⊤).elim eq_of_le_of_ge
  tfae_have 3 → 2 := fun h ↦ (h.symm ▸ rmk4d10₀ μ ⊤).elim eq_of_le_of_ge
  tfae_finish



/-- `prop4d16₂` is the main bridge: under `μ.IsSlopeLike` and both chain conditions,
  Nash equilibrium is equivalent to the equality `μmin μ ⊤ = μmax μ ⊤`.

  The proof packages the slope-like axiom into weak slope-like data on restrictions,
  and then combines `prop4d11₁` and `prop4d11₂` with the earlier characterisations.
-/
lemma prop4d16₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSlopeLike)
(h₁ : μ.WeakACC) (h₂ : μ.StrongDCC) :
μmin μ ⊤ = μmax μ ⊤ ↔ NashEquilibrium μ := by
  have : ∀ (z : StrictIntvl ℒ) (hz : z.right < ⊤), μ z ≤
    μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ ∨
    μ ⟨z.right, ⊤, hz⟩ ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ :=
    fun z hz ↦ (hμ.slopelike z.left z.right ⊤ ⟨z.lt, hz⟩).1.imp_right le_of_lt
  have hle : μAstar μ ≤ μBstar μ := impl.prop4d1₂ ℒ S μ (h₁ := h₁) (h₂ := { le_or_le := this})
  exact ⟨fun h ↦ {nash_eq := eq_of_le_of_ge hle <| prop4d11₁ μ h},
    fun h ↦ prop4d11₂ μ h₁ { le_or_le := this} h₂ { le_or_le := fun z hz ↦
      ((hμ.slopelike ⊥ z.left z.right ⟨hz, z.lt⟩).2.2.1.imp_left le_of_lt).symm}
      h.nash_eq.symm.le⟩



/-- `prop4d18₁` shows that semistability implies the best-response inequality
  `μBstar μ ≤ μAstar μ` in a linearly ordered setting.
-/
lemma prop4d18₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSemistable) : μBstar μ ≤ μAstar μ := by
  rw [PayoffFunction.isSemistable_iff_isBreakpoint_top] at hμ
  have hstep : ∀ (x : ℒ) (hx : ⊥ < x), μA μ ⟨⊥, x, hx⟩ ≤ μAstar μ := fun x hx ↦
    le_of_not_gt <|
      hμ.not_lt x (StrictIntvl.mem_top x) (Ne.symm <| bot_lt_iff_ne_bot.1 hx)
  refine iSup₂_le fun x hx ↦ le_trans ?_ (hstep x hx.1)
  exact le_iInf₂ fun y hy ↦ iInf₂_le_of_le y hy (rmk4d10₀ μ ⟨y, x, hy.2⟩).2



/-- `prop4d18₂` deduces Nash equilibrium from semistability together with either
  (WACC + WSL₁) or (WDCC + WSL₂).
-/
lemma prop4d18₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSemistable)
(h : (μ.WeakACC ∧ μ.WeakSlopeLikeAtTop) ∨
  (μ.StrongDCC ∧ μ.WeakSlopeLikeAtBot)) :
NashEquilibrium μ :=
  {nash_eq := eq_of_le_of_ge
    (h.elim (fun h ↦ impl.prop4d1₂ ℒ S μ (h₁ := h.1) (h₂ := h.2))
      (fun h ↦ impl.prop4d3₂ μ (h₁ := h.1) (h₂ := h.2)))
    (prop4d18₁ μ hμ)}



/-- `prop4d20` shows that Nash equilibrium forces semistability, provided that on each
  bottom-anchored restriction `Resμ` we have WACC and the first weak slope-like axiom.
-/
lemma prop4d20 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
(h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) → PayoffFunction.WeakACC (Resμ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ μ))
(h₂ : ∀ x : ℒ, (hx : x ≠ ⊥) →
  PayoffFunction.WeakSlopeLikeAtTop (Resμ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩ μ)) :
NashEquilibrium μ → μ.IsSemistable := by
  intro h
  replace h := h.nash_eq
  have key : ∀ (x : ℒ) (hx : ⊥ < x), μA μ ⟨⊥, x, hx⟩ = μmin μ ⟨⊥, x, hx⟩ := by
    intro x hx
    have := impl.prop4d1₁ ↥(⟨⊥, x, hx⟩ : StrictIntvl ℒ) S (Resμ ⟨⊥, x, hx⟩ μ)
      (h₁ := h₁ x hx.ne') (h₂ := h₂ x hx.ne')
    rwa [μAstar, μA_res_intvl, μmin_res_intvl, StrictIntvl.ofSub_top] at this
  have : (⨆ (x : ℒ) (hx : ⊥ < x), μA μ ⟨⊥, x, hx⟩) = μBstar μ :=
    le_antisymm (iSup₂_le fun x hx ↦ le_iSup₂_of_le x ⟨hx, le_top⟩ (key x hx).le)
      (iSup₂_le fun x hx ↦ le_iSup₂_of_le x hx.1 (key x hx.1).ge)
  replace : ∀ x : ℒ, (hx : x ≠ ⊥) → μA μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ ≤ μA μ ⊤ := by
    rw [← h] at this
    simp only [μAstar] at this
    intro x hx
    rw [← this]
    exact le_iSup₂_of_le x (bot_lt_iff_ne_bot.2 hx) le_rfl
  exact { not_lt := fun x hx ↦ (this x hx.ne').not_gt}



/-- `thm4d21` is the main “Section 4” synthesis theorem.

  It packages:
  * a TFAE chain relating the endpoint equalities and Nash equilibrium, and
  * two implication directions connecting semistability and Nash equilibrium.
-/
theorem thm4d21 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) (hμ : μ.IsSlopeLike)
(h₁ : μ.WeakACC) (h₂ : μ.StrongDCC) :
List.TFAE [
  μmax μ ⊤ = μ ⊤, μmin μ ⊤ = μ ⊤, μmin μ ⊤ = μmax μ ⊤, NashEquilibrium μ,
  ] ∧
(μ.IsSemistable → NashEquilibrium μ) ∧
((∀ x : ℒ, (hx : x ≠ ⊥) →
  PayoffFunction.WeakACC (Resμ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ μ)) →
  NashEquilibrium μ → μ.IsSemistable)
  := by
  constructor
  · have h16 := prop4d16₁ μ hμ
    tfae_have 1 ↔ 2 := h16.out 0 1
    tfae_have 2 ↔ 3 := h16.out 1 2
    tfae_have 3 ↔ 4 := prop4d16₂ μ hμ h₁ h₂
    tfae_finish
  · constructor
    · exact fun h ↦ prop4d18₂ μ h <| Or.inl ⟨h₁,
        { le_or_le := fun a b ↦ (hμ.slopelike a.left a.right ⊤ ⟨a.lt, b⟩).1.imp_right le_of_lt}⟩
    · exact fun h₁ ↦ prop4d20 μ h₁ fun x hx ↦
        { le_or_le := fun a b ↦ (hμ.slopelike a.left a.right x ⟨a.lt, b⟩).1.imp_right le_of_lt}

end impl

end HarderNarasimhan
