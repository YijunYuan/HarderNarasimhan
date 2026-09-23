/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolder.Defs

/-!
# Stability of the steps of a Jordan–Hölder filtration

For a slope-like payoff function satisfying the eventually-`⊤` descending chain condition,
the payoff inequalities in a Jordan–Hölder filtration characterize stability of its steps.
More precisely, a step with endpoints `a < b` is stable if and only if every `a < z < b`
satisfies `μ ⟨a, z, _⟩ < μ ⟨a, b, _⟩`. We assume that the codomain is a complete linear order
and `>` is well-founded on the lattice.

## Main results

* `HarderNarasimhan.PayoffFunction.piecewise_isStable_iff`: the equivalence for a finite
  strictly decreasing chain.
* `HarderNarasimhan.PayoffFunction.piecewise_isStable_of_payoff_lt` and
  `HarderNarasimhan.PayoffFunction.payoff_lt_of_piecewise_isStable`: the two implications.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S]
variable (μ : PayoffFunction ℒ S) [μ.IsSlopeLike] [μ.EventuallyTopDCC]
variable (f : ℕ → ℒ) {n : ℕ}

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- If replacing the upper endpoint of each step by a strictly intermediate point strictly
decreases the payoff, then every step is semistable. -/
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
      u.prop.1.lt_of_ne fun hc ↦ hu <| Subtype.coe_inj.1 hc.symm
    have hur : u.val < f i :=
      u.prop.2.lt_of_ne fun hc ↦ hu1.2.ne <| Subtype.coe_inj.1 hc
    exact le_of_lt <| ((inferInstance : μ.IsSlopeLike).seesaw_total_lt_right_iff hul hur).2
      (h i hi u.val hul hur)

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- If replacing the upper endpoint of each step by a strictly intermediate point strictly
decreases the payoff, then every step is stable. -/
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
      x.prop.1.lt_of_ne fun hc ↦ hx.ne' <| Subtype.coe_inj.1 hc.symm
    have hmin_step : (μ.restrict stepI).min ⊤ = (μ.restrict stepI) ⊤ :=
      min_top_eq_apply_iff.2 <| min_top_eq_max_top_iff_hasNashEquilibrium.2
        (piecewise_isSemistable_of_payoff_lt μ f hsa h i hi).hasNashEquilibrium
    simp only [min_restrict_apply, restrict_apply] at hmin_step
    simp only [A_restrict_apply, ← (inferInstance : μ.IsSlopeLike).min_eq_A]
    rw [hmin_step]
    exact ((min_le_apply (μ := μ) (I := ⟨f (i + 1), ↑x, hx_left⟩)).trans_lt <|
      h i hi x.val hx_left hx').ne

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- If every step is stable, replacing its upper endpoint by a strictly intermediate point
strictly decreases the payoff. -/
theorem payoff_lt_of_piecewise_isStable
    (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i)
    (hst : ∀ i : ℕ, (hi : i < n) →
      (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsStable) :
    ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
      μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ := by
  intro i hi z hz hz'
  let stepI : StrictIntvl ℒ :=
    ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩
  let midI : ↥stepI := ⟨z, hz.le, hz'.le⟩
  have hmid_ne_bot : ⊥ < midI :=
    bot_lt_iff_ne_bot.2 fun hc ↦ hz.ne' (congrArg Subtype.val hc)
  have hmid_ne_top : midI < ⊤ :=
    lt_top_iff_ne_top.2 fun hc ↦ hz'.ne (congrArg Subtype.val hc)
  have hNash_step := (hst i hi).toIsSemistable.hasNashEquilibrium
  have hmin_step : (μ.restrict stepI).min ⊤ = (μ.restrict stepI) ⊤ :=
    min_top_eq_apply_iff.2 (min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  have hmax_step : (μ.restrict stepI).max ⊤ = (μ.restrict stepI) ⊤ :=
    max_top_eq_apply_iff.2 (min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  -- Stability gives a strict inequality for the infimum of payoffs on the shorter interval.
  have hmin_lt : μ.min ⟨f (i + 1), z, hz⟩ <
      μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ := by
    have hstable := (not_lt.1 ((hst i hi).toIsSemistable.not_lt midI hmid_ne_bot)).lt_of_ne
      ((hst i hi).ne midI hmid_ne_bot hmid_ne_top)
    rw [A_top_eq_min_top, hmin_step] at hstable
    simp only [A_restrict_apply, restrict_apply,
      ← (inferInstance : μ.IsSlopeLike).min_eq_A] at hstable
    exact hstable
  have payoff_le_total : ∀ (u : ↥stepI) (hu : (⊥ : ↥stepI) < u),
      (μ.restrict stepI) ⟨⊥, u, hu⟩ ≤ (μ.restrict stepI) ⊤ := fun u hu ↦
    hmax_step ▸ le_iSup₂_of_le u ⟨hu, le_top⟩ le_rfl
  refine (payoff_le_total midI hmid_ne_bot).lt_of_ne ?_
  intro heq
  -- If the payoffs were equal, a smaller infimum would violate semistability.
  change μ ⟨f (i + 1), z, hz⟩ =
    μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ at heq
  rw [← heq] at hmin_lt
  obtain ⟨y, hy⟩ := iInf_lt_iff.1 hmin_lt
  obtain ⟨hy_mem, hy_payoff⟩ := iInf_lt_iff.1 hy
  have hy_left : f (i + 1) < y := by
    refine lt_of_le_of_ne hy_mem.1 fun heq ↦ ?_
    simp only [heq, lt_self_iff_false] at hy_payoff
  have hy_gt := ((inferInstance : μ.IsSlopeLike).seesaw_right_lt_total_iff
    hy_left hy_mem.2).1 hy_payoff
  rw [heq] at hy_gt
  exact hy_gt.not_ge (payoff_le_total ⟨y, hy_mem.1, (hy_mem.2.trans hz').le⟩ hy_left)

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- The steps of a finite strictly decreasing chain are stable if and only if replacing
the upper endpoint of any step by a strictly intermediate point strictly decreases its payoff. -/
theorem piecewise_isStable_iff (hsa : ∀ i j : ℕ, i < j → j ≤ n → f j < f i) :
    (∀ i : ℕ, (hi : i < n) →
        (μ.restrict ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩).IsStable) ↔
      ∀ i : ℕ, (hi : i < n) → ∀ z : ℒ, (h' : f (i + 1) < z) → z < f i →
        μ ⟨f (i + 1), z, h'⟩ < μ ⟨f (i + 1), f i, hsa i (i + 1) (lt_add_one i) hi⟩ :=
  ⟨payoff_lt_of_piecewise_isStable μ f hsa, piecewise_isStable_of_payoff_lt μ f hsa⟩

end PayoffFunction

end HarderNarasimhan
