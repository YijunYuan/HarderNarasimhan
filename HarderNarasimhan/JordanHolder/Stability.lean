/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolder.Defs

/-!
# Stability of the steps of a Jordan–Hölder filtration

This file relates the two ways of saying that the steps of a finite strictly decreasing
chain `f` are *stable*: the stability condition of `PayoffFunction.JordanHolderFiltration`
(refining a step through any strictly intermediate point strictly decreases the payoff) is
equivalent to stability, in the sense of `PayoffFunction.IsStable`, of the restriction of
`μ` to each step interval.

## Main results

* `PayoffFunction.piecewise_isStable_iff` : the equivalence.
* `PayoffFunction.piecewise_isStable_of_payoff_lt`,
  `PayoffFunction.payoff_lt_of_piecewise_isStable` : the two directions.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S]
variable (μ : PayoffFunction ℒ S) [μ.IsSlopeLike] [μ.EventuallyTopDCC]
variable (f : ℕ → ℒ) {n : ℕ}

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- If every strictly intermediate refinement of the steps of `f` strictly decreases the
payoff, then the restriction of `μ` to each step interval is semistable. -/
private lemma piecewise_isSemistable_of_payoff_lt
    (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i)
    (h : ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
      μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩) :
    ∀ i : ℕ, (hi : i < n) →
      (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsSemistable := by
  intro i hi
  apply isSemistable_of_hasNashEquilibrium (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
  apply min_top_eq_max_top_iff_hasNashEquilibrium.1
  apply min_top_eq_apply_iff.1
  apply eq_of_le_of_ge ?_ ?_
  · exact iInf₂_le ⊥ ⟨le_rfl, bot_lt_top⟩
  · refine le_iInf₂ fun u hu1 ↦ ?_
    simp only [restrict_apply]
    if hu : u = ⊥ then
      subst hu
      exact le_rfl
    else
    have hul : f (i + 1) < u.val :=
      lt_of_le_of_ne u.prop.1 fun hc ↦ hu <| Subtype.coe_inj.1 hc.symm
    have hur : u.val < f i :=
      lt_of_le_of_ne u.prop.2 fun hc ↦ hu1.2.ne <| Subtype.coe_inj.1 hc
    exact le_of_lt <| ((inferInstance : μ.IsSlopeLike).seesaw_total_lt_right_iff hul hur).2
      (h i hi u.val hul hur)

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- If every strictly intermediate refinement of the steps of `f` strictly decreases the
payoff, then the restriction of `μ` to each step interval is stable. -/
theorem piecewise_isStable_of_payoff_lt
    (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i)
    (h : ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
      μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩) :
    ∀ i : ℕ, (hi : i < n) →
      (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsStable := by
  intro i hi
  refine {
    toIsSemistable := piecewise_isSemistable_of_payoff_lt μ f hsa h i hi,
    ne := ?_ }
  · intro x hx hx'
    let stepI : StrictIntvl ℒ :=
      ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩
    have hx_left : f (i + 1) < x.val :=
      lt_of_le_of_ne x.prop.1 fun hc ↦ hx.ne' <| Subtype.coe_inj.1 hc.symm
    have hA_step : (μ.restrict stepI).A ⊤ = (μ.restrict stepI).min ⊤ :=
      A_top_eq_min_top
    have hA_x : (μ.restrict ⟨f (i + 1), x.val, hx_left⟩).A ⊤ =
        (μ.restrict ⟨f (i + 1), x.val, hx_left⟩).min ⊤ :=
      A_top_eq_min_top
    simp only [A_restrict_apply, min_restrict_apply] at *
    rw [hA_step]
    replace hA_x : μ.A (StrictIntvl.ofSub ⟨⊥, x, hx⟩) =
      μ.min (StrictIntvl.ofSub ⟨⊥, x, hx⟩) := hA_x
    rw [hA_x]
    have hss := piecewise_isSemistable_of_payoff_lt μ f hsa h i hi
    have hNash_step := hss.hasNashEquilibrium
    have hmin_step : (μ.restrict stepI).min ⊤ = (μ.restrict stepI) ⊤ :=
      min_top_eq_apply_iff.2
        (min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
    simp only [min_restrict_apply, restrict_apply] at hmin_step
    rw [hmin_step]
    exact ne_of_lt <| lt_of_le_of_lt
      (min_le_apply (μ := μ) (I := ⟨f (i + 1), ↑x, hx_left⟩)) <|
      h i hi x.val hx_left hx'

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- Conversely, if the restriction of `μ` to each step interval of `f` is stable, then every
strictly intermediate refinement of the steps strictly decreases the payoff. -/
theorem payoff_lt_of_piecewise_isStable
    (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i)
    (hst : ∀ i : ℕ, (hi : i < n) →
      (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsStable) :
    ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
      μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ := by
  intro i hi z hz hz'
  let stepI : StrictIntvl ℒ :=
    ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩
  let midI : ↥stepI := ⟨z, le_of_lt hz, le_of_lt hz'⟩
  have hmid_ne_bot : ⊥ < midI :=
    bot_lt_iff_ne_bot.2 fun hc ↦ ne_of_gt hz (congrArg Subtype.val hc)
  have hmid_ne_top : midI < ⊤ :=
    lt_top_iff_ne_top.2 fun hc ↦ ne_of_lt hz' (congrArg Subtype.val hc)
  have hss := (hst i hi).toIsSemistable.not_lt midI hmid_ne_bot
  simp only [not_lt] at hss
  have hst' : (μ.restrict stepI).A ⟨⊥, midI, hmid_ne_bot⟩ < (μ.restrict stepI).A ⊤ :=
    lt_of_le_of_ne hss ((hst i hi).ne midI hmid_ne_bot hmid_ne_top)
  have hA_step : (μ.restrict stepI).A ⊤ = (μ.restrict stepI).min ⊤ :=
    A_top_eq_min_top
  rw [hA_step] at hst'
  have hA_mid : (μ.restrict ⟨f (i + 1), z, hz⟩).A ⊤ =
      (μ.restrict ⟨f (i + 1), z, hz⟩).min ⊤ :=
    A_top_eq_min_top
  have hb : (μ.restrict ⟨f (i + 1), f i, gt_trans hz' hz⟩).A ⟨⊥, midI, hmid_ne_bot⟩ =
      (μ.restrict ⟨f (i + 1), z, hz⟩).A ⊤ := by
    simp only [A_restrict_apply, min_restrict_apply] at *
    rfl
  rw [hb, hA_mid] at hst'
  have hNash_step := (hst i hi).toIsSemistable.hasNashEquilibrium
  have hmin_step : (μ.restrict stepI).min ⊤ = (μ.restrict stepI) ⊤ :=
    min_top_eq_apply_iff.2
      (min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  rw [hmin_step] at hst'
  have hmax_step : (μ.restrict stepI).max ⊤ = (μ.restrict stepI) ⊤ :=
    max_top_eq_apply_iff.2
      (min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  simp only [min_restrict_apply, restrict_apply] at hst'
  have hsSup_step : ∀ (u : ↥stepI) (hu : (⊥ : ↥stepI) < u),
      (μ.restrict stepI) ⟨⊥, u, hu⟩ ≤ (μ.restrict stepI) ⊤ := fun u hu ↦
    hmax_step ▸ le_iSup₂_of_le u ⟨hu, le_top⟩ le_rfl
  have hsSup_step_bak := hsSup_step
  have hsSup_mid := hsSup_step midI hmid_ne_bot
  have hsSup_mid' : μ ⟨f (i + 1), z, hz⟩ ≤ μ ⟨f (i + 1), f i,
      hsa i (i + 1) (lt_add_one i) hi⟩ := hsSup_mid
  refine lt_of_le_of_ne hsSup_mid' ?_
  by_contra hc
  replace hst' : μ.min ⟨f (i + 1), z, hz⟩ <
      μ ⟨f (i + 1), f i, gt_trans hz' hz⟩ := hst'
  rw [← hc] at hst'
  obtain ⟨y, hy⟩ := iInf_lt_iff.1 hst'
  obtain ⟨hy1, hs⟩ := iInf_lt_iff.1 hy
  have := ((inferInstance : μ.IsSlopeLike).seesaw_right_lt_total_iff
    (x := f (i + 1)) (y := y) (z := z)
    (lt_of_le_of_ne hy1.1 fun hc ↦ by simp only [hc, lt_self_iff_false] at hs)
    hy1.2).1 hs
  simp only [hc] at this
  have res := hsSup_step_bak ⟨y, hy1.1, le_of_lt <| lt_of_le_of_lt hy1.2.le hz'⟩ (by
    refine lt_of_le_of_ne hy1.1 ?_
    by_contra hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    simp only [← hc, StrictIntvl.val_bot, stepI, lt_self_iff_false] at hs)
  simp only [stepI, restrict_apply] at res
  exact (not_le_of_gt this) res

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- The stability condition of `PayoffFunction.JordanHolderFiltration` is equivalent to
stability of the restriction of `μ` to each step interval: for a chain `f` strictly
decreasing up to `n`, every strictly intermediate refinement of the steps strictly
decreases the payoff iff each restricted payoff function is stable. -/
theorem piecewise_isStable_iff (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i) :
    (∀ i : ℕ, (hi : i < n) →
        (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsStable) ↔
      ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
        μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ :=
  ⟨payoff_lt_of_piecewise_isStable μ f hsa, piecewise_isStable_of_payoff_lt μ f hsa⟩

end PayoffFunction

end HarderNarasimhan
