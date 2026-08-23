/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.NashEquilibrium.Defs
import HarderNarasimhan.FirstMoverAdvantage.Impl
import HarderNarasimhan.FirstMoverAdvantage.Defs
import HarderNarasimhan.SlopeLike.Defs
import HarderNarasimhan.Semistability.Translation
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

/-- `rmk4d10₀` records the basic bounds: for any interval `I`, `μmin μ I ≤ μ I ≤ μmax μ I`.
  This is a direct consequence of the defining `sInf`/`sSup` characterisations.
-/
lemma rmk4d10₀ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
∀ I : Intvl ℒ, μmin μ I ≤ μ I ∧ μ I ≤ μmax μ I :=
  fun I ↦ ⟨sInf_le ⟨I.left, ⟨I.left_mem, I.lt.ne⟩, rfl⟩,
    le_sSup ⟨I.right, ⟨I.right_mem, I.lt.ne⟩, rfl⟩⟩



/-- `rmk4d10₁` rewrites the inequality `μBstar μ ≤ μAstar μ` as an explicit family of
  inequalities comparing the extremal values on bottom- and top-anchored intervals.
  This is a convenient “unfolded” form for later arguments.
-/
lemma rmk4d10₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
μBstar μ ≤ μAstar μ ↔
  ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) →
    μmin μ ⟨⊥, y,hy⟩ ≤ μmax μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx⟩ := by
  constructor
  · intro h x hx y hy
    simp only [μBstar, μAstar] at h
    unfold μA μB at h
    apply sSup_le_iff.1 at h
    simp only [ne_eq, Set.mem_ofPred_eq, le_sInf_iff, forall_exists_index] at h
    exact h (μmin μ ⟨⊥, y, hy⟩) y ⟨Intvl.mem_top y, ne_of_lt hy⟩ rfl
      (μmax μ ⟨x, ⊤, lt_top_iff_ne_top.2 hx⟩) x ⟨Intvl.mem_top x, hx⟩ rfl
  · refine fun h ↦ sSup_le_iff.2 ?_
    simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index]
    refine fun b x hx h' ↦ h' ▸ le_sInf_iff.2 ?_
    simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index]
    exact fun _ x' _ h'' ↦ h'' ▸ h x' (by tauto) x _



/-- `rmk4d10₂` specialises Nash equilibrium to the case where we have a weak ascending
  chain condition together with the first weak slope-like axiom.

  Under these hypotheses, Nash equilibrium is equivalent to a single family of
  inequalities comparing `μmin` on bottom-anchored intervals with `μmin` on `⊤`.
-/
lemma rmk4d10₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : WeakAscendingChainCondition μ) (h₂ : WeakSlopeLike₁ μ) :
NashEquilibrium μ ↔
  ∀ y : ℒ, (hy : y ≠ ⊥) → μmin μ ⟨⊥, y,bot_lt_iff_ne_bot.2 hy⟩ ≤ μmin μ ⊤ := by
  constructor
  · intro h y hy
    replace h := h.nash_eq
    rw [impl.prop4d1₁ ℒ S μ h₁.wacc h₂.wsl₁] at h
    simp only [Intvl.left_top, μBstar, μB, ne_eq] at h
    rw [h]
    exact le_sSup ⟨y, ⟨Intvl.mem_top y, Ne.symm hy⟩, rfl⟩
  · intro h
    refine {nash_eq := ?_}
    rw [impl.prop4d1₁ ℒ S μ h₁.wacc h₂.wsl₁]
    simp only [μBstar, μB, ne_eq]
    exact eq_of_le_of_ge (le_sSup ⟨⊤, ⟨Intvl.mem_top ⊤, bot_ne_top⟩, rfl⟩)
      (sSup_le fun b ⟨h1, h2, h3⟩ ↦ h3 ▸ (h h1 <| Ne.symm h2.2))



/-- `rmk4d10₃` is the dual counterpart of `rmk4d10₂`.

  Assuming a strong descending chain condition and the second weak slope-like axiom,
  Nash equilibrium is equivalent to a family of inequalities comparing `μmax` on
  `⊤` with `μmax` on top-anchored intervals.
-/
lemma rmk4d10₃ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : StrongDescendingChainCondition μ) (h₂ : WeakSlopeLike₂ μ) :
NashEquilibrium μ ↔
  ∀ y : ℒ, (hy : y ≠ ⊤) → μmax μ ⊤ ≤ μmax μ ⟨y, ⊤,lt_top_iff_ne_top.2 hy⟩ := by
  constructor
  · intro h y hy
    replace h := h.nash_eq
    rw [impl.prop4d3₁ μ h₁.wdcc h₂.wsl₂] at h
    rw [← h]
    unfold μAstar μA
    exact sInf_le ⟨y, ⟨Intvl.mem_top y, hy⟩, rfl⟩
  · intro h
    refine {nash_eq := ?_}
    rw [impl.prop4d3₁ μ h₁.wdcc h₂.wsl₂]
    simp only [μAstar, μA, ne_eq]
    exact eq_of_le_of_ge (sInf_le ⟨⊥, ⟨Intvl.mem_top ⊥, bot_ne_top⟩, rfl⟩)
      (le_sInf fun b ⟨h1, h2, h3⟩ ↦ h3 ▸ (h h1 h2.2))



/-- `prop4d11₁` shows that if the global extremal values on `⊤` coincide, then
  the best-response inequality `μBstar μ ≤ μAstar μ` holds.
-/
lemma prop4d11₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
μmin μ ⊤ = μmax μ ⊤ → μBstar μ ≤ μAstar μ := by
  have h₁ : μBstar μ ≤ μmax μ ⊤ := by
    unfold μBstar μB μmax
    exact sSup_le fun b ⟨hb1, hb2, hb3⟩ ↦ hb3 ▸ le_trans
      (rmk4d10₀ μ ⟨⊥, hb1, bot_lt_iff_ne_bot.2 <| Ne.symm hb2.2⟩).1 <|
      le_sSup ⟨hb1, ⟨Intvl.mem_top hb1, hb2.2⟩, rfl⟩
  have h₂ : μmin μ ⊤ ≤ μAstar μ := by
    unfold μAstar μA μmin
    exact le_sInf fun b ⟨hb1, hb2, hb3⟩ ↦ hb3 ▸ le_trans
      (sInf_le ⟨hb1, ⟨Intvl.mem_top hb1, hb2.2⟩, rfl⟩)
      (rmk4d10₀ μ ⟨hb1, ⊤, lt_top_iff_ne_top.2 <| hb2.2⟩).2
  exact fun h ↦ h₁.trans (h ▸ h₂)



/-- `prop4d11₂` is a converse direction: under the weak chain/slope hypotheses on both
  sides, the inequality `μBstar μ ≤ μAstar μ` forces equality of the global extremal
  values `μmin μ ⊤` and `μmax μ ⊤`.
-/
lemma prop4d11₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : WeakAscendingChainCondition μ) (h₂ : WeakSlopeLike₁ μ)
(h₁' : StrongDescendingChainCondition μ) (h₂' : WeakSlopeLike₂ μ) :
μBstar μ ≤ μAstar μ → μmin μ ⊤ = μmax μ ⊤ :=
  fun h ↦ eq_of_le_of_ge (le_trans (rmk4d10₀ μ ⊤).1 (rmk4d10₀ μ ⊤).2) <|
    (impl.prop4d3₁ μ h₁'.wdcc h₂'.wsl₂) ▸ (impl.prop4d1₁ ℒ S μ h₁.wacc h₂.wsl₁) ▸ h



/-- `prop4d12` derives the equality `μmin μ ⊤ = μmax μ ⊤` from the
  stronger equality `μmax μ ⊤ = μ ⊤`, provided a pointwise dichotomy
  that rules out “intermediate” points simultaneously satisfying both comparisons.
-/
lemma prop4d12 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩) :
μmax μ ⊤ = μ ⊤ → μmin μ ⊤ = μmax μ ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge (rmk4d10₀ μ ⊤).1
    (le_sInf fun b ⟨hb1, hb2, hb3⟩ ↦ hb3 ▸ ?_)
  by_cases hbot : hb1 = ⊥
  · subst hbot
    exact le_rfl
  refine Or.resolve_left (h hb1 ⟨hbot, hb2.2⟩) (not_not.2 ?_)
  exact h' ▸ le_sSup ⟨hb1, ⟨Intvl.mem_top hb1, Ne.symm hbot⟩, rfl⟩



/-- `rmk4d13` shows that the dichotomy assumption used in `prop4d12` follows from a
  genuine `SlopeLike μ` structure.
-/
lemma rmk4d13 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (hμ : SlopeLike μ) :
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩ :=
  fun x hx ↦ ((hμ.slopelike ⊥ x ⊤
    ⟨bot_lt_iff_ne_bot.2 hx.1,lt_top_iff_ne_top.2 hx.2⟩).2.2.1).imp_left not_le_of_gt



/-- `prop4d14` is the dual analogue of `prop4d12`: starting from `μmin μ ⊤ = μ ⊤`
  and a suitable dichotomy, it deduces `μmax μ ⊤ = μmin μ ⊤`.
-/
lemma prop4d14 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
  ¬ μ ⊤ ≤ μ ⟨x, ⊤,lt_top_iff_ne_top.2 hx.2⟩) :
μmin μ ⊤ = μ ⊤ → μmax μ ⊤ = μmin μ ⊤ := by
  refine fun h' ↦ h' ▸ eq_of_le_of_ge
    (sSup_le fun b ⟨hb1, hb2, hb3⟩ ↦ hb3 ▸ ?_) (rmk4d10₀ μ ⊤).2
  by_cases htop : hb1 = ⊤
  · subst htop
    exact le_rfl
  refine Or.resolve_right (h hb1 ⟨Ne.symm hb2.2, htop⟩) (not_not.2 ?_)
  exact h' ▸ sInf_le ⟨hb1, ⟨Intvl.mem_top hb1, htop⟩, rfl⟩



/-- `rmk4d15` shows that the dichotomy assumption used in `prop4d14` also follows from
  a `SlopeLike μ` structure.
-/
lemma rmk4d15 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (hμ : SlopeLike μ) :
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
(μ : Intvl ℒ → S) (hμ : SlopeLike μ) :
List.TFAE [
  μmax μ ⊤ = μ ⊤, μmin μ ⊤ = μ ⊤, μmin μ ⊤ = μmax μ ⊤
  ] := by
  tfae_have 1 → 3 := prop4d12 μ (rmk4d13 μ hμ)
  tfae_have 2 → 3 := fun h ↦ (prop4d14 μ (rmk4d15 μ hμ) h).symm
  tfae_have 3 → 1 := fun h ↦ (h ▸ rmk4d10₀ μ ⊤).elim eq_of_le_of_ge
  tfae_have 3 → 2 := fun h ↦ (h.symm ▸ rmk4d10₀ μ ⊤).elim eq_of_le_of_ge
  tfae_finish



/-- `prop4d16₂` is the main bridge: under `SlopeLike μ` and both chain conditions,
  Nash equilibrium is equivalent to the equality `μmin μ ⊤ = μmax μ ⊤`.

  The proof packages the slope-like axiom into weak slope-like data on restrictions,
  and then combines `prop4d11₁` and `prop4d11₂` with the earlier characterisations.
-/
lemma prop4d16₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (hμ : SlopeLike μ)
(h₁ : WeakAscendingChainCondition μ) (h₂ : StrongDescendingChainCondition μ) :
μmin μ ⊤ = μmax μ ⊤ ↔ NashEquilibrium μ := by
  have : ∀ (z : Intvl ℒ) (hz : z.right < ⊤), μ z ≤
    μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ ∨
    μ ⟨z.right, ⊤, hz⟩ ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ :=
    fun z hz ↦ (hμ.slopelike z.left z.right ⊤ ⟨z.lt, hz⟩).1.imp_right le_of_lt
  exact ⟨fun h ↦ {nash_eq := eq_of_le_of_ge (impl.prop4d1₂ ℒ S μ h₁.wacc this) <| prop4d11₁ μ h},
    fun h ↦ prop4d11₂ μ h₁ {wsl₁ := this} h₂ {wsl₂ := fun z hz ↦
      ((hμ.slopelike ⊥ z.left z.right ⟨hz, z.lt⟩).2.2.1.imp_left le_of_lt).symm}
      h.nash_eq.symm.le⟩



/-- `prop4d18₁` shows that semistability implies the best-response inequality
  `μBstar μ ≤ μAstar μ` in a linearly ordered setting.
-/
lemma prop4d18₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S) (hμ : Semistable μ) : μBstar μ ≤ μAstar μ := by
  rw [semistable_iff] at hμ
  have : sSup {μA μ ⟨⊥, x,hx⟩ | (x : ℒ) (hx : ⊥ < x)} ≤ μAstar μ :=
    sSup_le fun b ⟨hb1, hb2, hb3⟩ ↦ le_of_not_gt <| hb3 ▸
      hμ.out.choose_spec.choose_spec.1 hb1 (Intvl.mem_top hb1) (Ne.symm <| bot_lt_iff_ne_bot.1 hb2)
  refine le_trans (sSup_le_sSup_of_isCofinalFor ?_) this
  rintro x ⟨hx1,⟨hx2,hx3⟩⟩
  refine ⟨μA μ ⟨⊥, hx1, bot_lt_iff_ne_bot.2 <| Ne.symm hx2.2⟩,
    ⟨hx1, bot_lt_iff_ne_bot.2 <| Ne.symm hx2.2, rfl⟩, hx3 ▸ sInf_le_sInf_of_isCoinitialFor ?_⟩
  rintro y ⟨hy1,⟨hy2,hy3⟩⟩
  exact ⟨μ ⟨hy1, hx1, lt_of_le_of_ne hy2.1.2 hy2.2⟩, ⟨hy1, hy2, rfl⟩,
    hy3 ▸ (rmk4d10₀ μ ⟨hy1, hx1, lt_of_le_of_ne hy2.1.2 hy2.2⟩).2⟩



/-- `prop4d18₂` deduces Nash equilibrium from semistability together with either
  (WACC + WSL₁) or (WDCC + WSL₂).
-/
lemma prop4d18₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S) (hμ : Semistable μ)
(h : (WeakAscendingChainCondition μ ∧ WeakSlopeLike₁ μ) ∨
  (StrongDescendingChainCondition μ ∧ WeakSlopeLike₂ μ)) :
NashEquilibrium μ :=
  {nash_eq := eq_of_le_of_ge
    (h.elim (fun h ↦ impl.prop4d1₂ ℒ S μ h.1.wacc h.2.wsl₁)
      (fun h ↦ impl.prop4d3₂ μ h.1.wdcc h.2.wsl₂))
    (prop4d18₁ μ hμ)}



/-- `prop4d20` shows that Nash equilibrium forces semistability, provided that on each
  bottom-anchored restriction `Resμ` we have WACC and the first weak slope-like axiom.
-/
lemma prop4d20 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) → WeakAscendingChainCondition (Resμ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ μ))
(h₂ :  ∀ x : ℒ, (hx : x ≠ ⊥) → WeakSlopeLike₁ (Resμ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ μ)) :
NashEquilibrium μ → Semistable μ := by
  intro h
  replace h := h.nash_eq
  have : sSup {μA μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ | (x : ℒ) (hx : x ≠ ⊥)} = μBstar μ := by
    unfold μBstar μB
    congr 1; ext
    constructor
    · simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index]
      intro x hx hx'
      rw [← hx']
      use x, ⟨Intvl.mem_top _,Ne.symm hx⟩
      refine Eq.trans ?_ <| Eq.trans (Eq.symm <| impl.prop4d1₁
        ↥(⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩ : Intvl ℒ) S (Resμ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩ μ)
        (h₁ x hx).wacc (h₂ x hx).wsl₁) ?_
      · simp only [μmin, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          exact ⟨⟨ha1,ha2.1⟩, ⟨Intvl.mem_top _,Subtype.coe_ne_coe.1 ha2.2⟩, ha3⟩
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          exact ⟨ha1, ⟨Intvl.mem_top ha1,Subtype.coe_ne_coe.2 ha2.2⟩, ha3⟩
      · simp only [μAstar, μA, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          refine ⟨ha1, ⟨Intvl.mem_top ha1,Subtype.coe_ne_coe.2 ha2.2⟩, ha3 ▸ ?_⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨⟨hb1, ⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩, hb3⟩
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩, hb3⟩
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          refine ⟨⟨ha1,ha2.1⟩, ⟨Intvl.mem_top _,Subtype.coe_ne_coe.1 ha2.2⟩, ha3 ▸ ?_⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩, hb3⟩
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨⟨hb1,⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩, hb3⟩
    · simp only [ne_eq, Set.mem_ofPred_eq, forall_exists_index]
      intro x hx hx'
      rw [← hx']
      use x, Ne.symm hx.2
      refine Eq.trans ?_ <| Eq.trans (impl.prop4d1₁ ↥(⟨⊥, x, bot_lt_iff_ne_bot.2 <|
        Ne.symm hx.2⟩ : Intvl ℒ) S (Resμ ⟨⊥, x, bot_lt_iff_ne_bot.2 <| Ne.symm hx.2⟩ μ)
        (h₁ x <| Ne.symm hx.2).wacc (h₂ x <| Ne.symm hx.2).wsl₁) ?_
      · simp only [μA, ne_eq, μAstar]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          refine ⟨⟨ha1,ha2.1⟩, ⟨Intvl.mem_top _,Subtype.coe_ne_coe.1 ha2.2⟩, ha3 ▸ ?_⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩, hb3⟩
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨⟨hb1,⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩, hb3⟩
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          refine ⟨ha1, ⟨Intvl.mem_top ha1,Subtype.coe_ne_coe.2 ha2.2⟩, ha3 ▸ ?_⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨⟨hb1, ⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩, hb3⟩
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            exact ⟨hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩, hb3⟩
      · simp only [μmin, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          exact ⟨ha1, ⟨Intvl.mem_top ha1,Subtype.coe_ne_coe.2 ha2.2⟩, ha3⟩
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          exact ⟨⟨ha1,ha2.1⟩, ⟨Intvl.mem_top _,Subtype.coe_ne_coe.1 ha2.2⟩, ha3⟩
  replace : ∀ x : ℒ, (hx : x ≠ ⊥) → μA μ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ ≤ μA μ ⊤ := by
    rw [← h] at this
    simp only [ne_eq, μAstar] at this
    intro x hx
    rw [← this]
    exact le_sSup ⟨x, hx, rfl⟩
  exact {semistable := fun x hx ↦ (this x hx.ne').not_gt}



/-- `thm4d21` is the main “Section 4” synthesis theorem.

  It packages:
  * a TFAE chain relating the endpoint equalities and Nash equilibrium, and
  * two implication directions connecting semistability and Nash equilibrium.
-/
theorem thm4d21 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S) (hμ : SlopeLike μ)
(h₁ : WeakAscendingChainCondition μ) (h₂ : StrongDescendingChainCondition μ) :
List.TFAE [
  μmax μ ⊤ = μ ⊤, μmin μ ⊤ = μ ⊤, μmin μ ⊤ = μmax μ ⊤, NashEquilibrium μ,
  ] ∧
(Semistable μ → NashEquilibrium μ) ∧
((∀ x : ℒ, (hx : x ≠ ⊥) →
  WeakAscendingChainCondition (Resμ ⟨⊥, x,bot_lt_iff_ne_bot.2 hx⟩ μ)) →
  NashEquilibrium μ → Semistable μ)
  := by
  constructor
  · have h16 := prop4d16₁ μ hμ
    tfae_have 1 ↔ 2 := h16.out 0 1
    tfae_have 2 ↔ 3 := h16.out 1 2
    tfae_have 3 ↔ 4 := prop4d16₂ μ hμ h₁ h₂
    tfae_finish
  · constructor
    · exact fun h ↦ prop4d18₂ μ h <| Or.inl ⟨h₁,
        {wsl₁ := fun a b ↦ (hμ.slopelike a.left a.right ⊤ ⟨a.lt, b⟩).1.imp_right le_of_lt}⟩
    · exact fun h₁ ↦ prop4d20 μ h₁ fun x hx ↦
        {wsl₁ := fun a b ↦ (hμ.slopelike a.left a.right x ⟨a.lt, b⟩).1.imp_right le_of_lt}

end impl

end HarderNarasimhan
