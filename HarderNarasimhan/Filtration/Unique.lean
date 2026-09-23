/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Exists

/-!
# Uniqueness of Harder–Narasimhan filtrations

For a convex payoff function with a complete linearly ordered codomain, the
Harder–Narasimhan filtration is unique under the chain conditions used in
`HarderNarasimhan/Filtration/Exists.lean`. Every such filtration equals the one obtained by
successively taking greatest breakpoints.

We also state existence and uniqueness in terms of finite `RelSeries` of semistable
intervals from `⊥` to `⊤`. In this formulation, the successive `μ.A`-values satisfy
`¬ aᵢ ≤ aᵢ₊₁`; for a linearly ordered codomain, they strictly decrease.

## Main results

* A `Unique` instance for `μ.HarderNarasimhanFiltration`.
* `HarderNarasimhan.PayoffFunction.exists_relSeries_semistableRel`: existence of a semistable
  series satisfying the successive-value condition, for an admissible payoff function.
* `HarderNarasimhan.PayoffFunction.existsUnique_relSeries_semistableRel`: uniqueness of
  this series for a complete linearly ordered codomain.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*}

section Unique

variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} [μ.ADCC] [μ.IsConvex]

open Classical in
/-- Every Harder–Narasimhan filtration equals the filtration obtained by taking greatest
breakpoints. -/
private theorem eq_hnFiltration (F : μ.HarderNarasimhanFiltration) : F = μ.hnFiltration := by
  have hμcvx : μ.IsConvexOn ⊤ := inferInstance
  have strict_growth : ∀ i j : ℕ, i < j → j ≤ F.length → F i < F j :=
    fun i j hij hj ↦ F.strictMonoOn (hij.le.trans hj) hj hij
  have step_breakpoint : ∀ j : ℕ, (hj : j < F.length) →
      μ.IsBreakpoint ⟨F j, F (j + 1), strict_growth j (j + 1) (lt_add_one j) hj⟩
        (F (j + 1)) :=
    fun j hj ↦ isBreakpoint_right_iff.2 (F.piecewise_isSemistable j hj)
  have slopes_strictAnti : ∀ i j : ℕ, (hij : i < j) → (hj : j < F.length) →
      μ.A ⟨F i, F (i + 1), strict_growth i (i + 1) (lt_add_one i) (by omega)⟩ >
      μ.A ⟨F j, F (j + 1), strict_growth j (j + 1) (lt_add_one j) hj⟩ := by
    intro i
    apply Nat.le_induction
    · exact fun hj ↦ lt_of_not_ge (F.not_A_le_succ i hj)
    · intro j hij ih hj
      exact (lt_of_not_ge (F.not_A_le_succ j hj)).trans (ih (Nat.lt_of_succ_lt hj))
  refine HarderNarasimhanFiltration.ext fun k ↦ ?_
  induction k with
  | zero => exact F.head_eq_bot.trans μ.hnFiltration.head_eq_bot.symm
  | succ n hn =>
    by_cases hnext : n + 1 ≤ F.length
    · -- Find the first step of F containing the next canonical breakpoint.
      have hcover : ∃ N : ℕ, N ≥ n + 1 ∧ μ.hnFiltration (n + 1) ≤ F N :=
        ⟨F.length, hnext, le_top.trans (F.eq_top_of_length_le le_rfl).ge⟩
      let i : ℕ := Nat.find hcover
      obtain ⟨hn_le_i, hcanonical_le⟩ : n + 1 ≤ i ∧ μ.hnFiltration (n + 1) ≤ F i :=
        Nat.find_spec hcover
      have hi_pos : 0 < i := Nat.zero_lt_of_lt hn_le_i
      have hi_length : i ≤ F.length :=
        Nat.find_min' hcover ⟨hnext, le_top.trans (F.eq_top_of_length_le le_rfl).ge⟩
      have hprev_length : i - 1 < F.length := Nat.sub_one_lt_of_le hi_pos hi_length
      have hcanonical_growth : μ.hnFiltration n < μ.hnFiltration (n + 1) :=
        μ.hnFiltration.lt_succ_of_ne_top
          (hn ▸ F.ne_top_of_lt (lt_of_lt_of_le (lt_add_one n) hnext))
      have hnot_le_prev : ¬ μ.hnFiltration (n + 1) ≤ F (i - 1) := by
        rcases not_and_or.1 (Nat.find_min hcover (Nat.sub_one_lt hi_pos.ne')) with hindex | hvalue
        · rw [show i - 1 = n by omega, hn]
          exact not_le_of_gt hcanonical_growth
        · exact hvalue
      have hbase_le_prev : μ.hnFiltration n ≤ F (i - 1) := by
        rw [← hn]
        exact F.monotone (Nat.le_sub_one_of_lt hn_le_i)
      have hstep_lt : F (i - 1) < F i :=
        strict_growth (i - 1) i (Nat.sub_one_lt hi_pos.ne') hi_length
      -- Convexity and semistability compare the canonical slope with this step's slope.
      have hslope_le : μ.A ⟨μ.hnFiltration n, μ.hnFiltration (n + 1), hcanonical_growth⟩ ≤
          μ.A ⟨F (i - 1), F i, hstep_lt⟩ := by
        have hprev_breakpoint := step_breakpoint (i - 1) hprev_length
        simp only [Nat.sub_one_add_one hi_pos.ne'] at hprev_breakpoint
        calc
          _ ≤ μ.A ⟨F (i - 1), μ.hnFiltration (n + 1) ⊔ F (i - 1),
              right_lt_sup.2 hnot_le_prev⟩ :=
            hμcvx.A_le_A_sup (StrictIntvl.mem_top (μ.hnFiltration (n + 1)))
              (StrictIntvl.mem_top (F (i - 1))) hnot_le_prev
              (le_inf hcanonical_growth.le hbase_le_prev)
          _ ≤ _ := le_of_not_gt (hprev_breakpoint.not_lt
            (μ.hnFiltration (n + 1) ⊔ F (i - 1))
            ⟨le_sup_right, sup_le hcanonical_le hstep_lt.le⟩
            (ne_of_lt (right_lt_sup.2 hnot_le_prev)))
      have hcanonical_breakpoint := mem_breakpoints.1
        (hnFiltration_succ_isGreatest_breakpoints (hcanonical_growth.trans_le le_top).ne).1
      have hi_eq : i = n + 1 := by
        refine eq_of_le_of_not_lt' hn_le_i ?_
        by_contra! hlt
        have hnext_lt : μ.hnFiltration n < F (n + 1) :=
          hn.ge.trans_lt (strict_growth n (n + 1) (lt_add_one n) hnext)
        have hslope_lt := slopes_strictAnti n (i - 1) (Nat.lt_sub_of_add_lt hlt) hprev_length
        simp only [hn, Nat.sub_one_add_one hi_pos.ne', gt_iff_lt] at hslope_lt
        exact hcanonical_breakpoint.not_lt (F (n + 1)) ⟨hnext_lt.le, le_top⟩ hnext_lt.ne
          (hslope_le.trans_lt hslope_lt)
      rw [hi_eq] at hcanonical_le
      have hnext_lt : μ.hnFiltration n < F (n + 1) := hcanonical_growth.trans_le hcanonical_le
      -- Both endpoints maximise the same value; the canonical breakpoint is greatest.
      refine le_antisymm (hcanonical_breakpoint.le_of_eq (F (n + 1))
        ⟨hnext_lt.le, le_top⟩ hnext_lt.ne ?_) hcanonical_le
      symm
      refine eq_of_le_of_not_lt ?_
        (hcanonical_breakpoint.not_lt (F (n + 1)) ⟨hnext_lt.le, le_top⟩ hnext_lt.ne)
      simpa only [hn] using le_of_not_gt ((step_breakpoint n hnext).not_lt
        (μ.hnFiltration (n + 1)) ⟨(hn.le.trans_lt hcanonical_growth).le, hcanonical_le⟩
        (hn.le.trans_lt hcanonical_growth).ne)
    · have hn_top : μ.hnFiltration n = ⊤ :=
        hn.symm.trans (F.eq_top_of_length_le (by omega))
      rw [F.eq_top_of_length_le (by omega)]
      exact (μ.hnFiltration.eq_top_of_length_le
        ((μ.hnFiltration.length_le_of_eq_top hn_top).trans (Nat.le_succ n))).symm

/-- Over a complete linear order the Harder–Narasimhan filtration is unique; the canonical
representative is `μ.hnFiltration`. -/
@[no_expose]
noncomputable instance : Unique (μ.HarderNarasimhanFiltration) where
  uniq := eq_hnFiltration

end Unique

section RelSeries

open Fin.NatCast

section Exists

variable [CompleteLattice S]

/-- There is a finite series of semistable intervals from `⊥` to `⊤` whose successive
`μ.A`-values satisfy `¬ aᵢ ≤ aᵢ₊₁`. -/
theorem exists_relSeries_semistableRel (μ : PayoffFunction ℒ S)
    [μ.ADCC] [μ.IsConvex] [μ.Admissible] :
    ∃ s : RelSeries μ.semistableRel,
      s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ i : ℕ, (hi : i + 1 < s.length) →
        ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
          μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩ := by
  refine ⟨{ toFun := fun n ↦ μ.hnFiltration n
            length := μ.hnFiltration.length
            step := fun i ↦
              ⟨μ.hnFiltration.strictMonoOn ((Nat.lt_add_one i.val).le.trans (Fin.is_le i.succ))
                  (Fin.is_le i.succ) (Nat.lt_add_one i.val),
                μ.hnFiltration.piecewise_isSemistable i.val i.prop⟩ },
    μ.hnFiltration.head_eq_bot, μ.hnFiltration.length_eq_top, ?_⟩
  refine fun i hi hc ↦ μ.hnFiltration.not_A_le_succ i hi ?_
  convert hc
  · exact congrArg μ.hnFiltration.toFun (Nat.mod_eq_of_lt <| lt_trans (Nat.lt_add_one i) <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg μ.hnFiltration.toFun (Nat.mod_eq_of_lt <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg μ.hnFiltration.toFun (Nat.mod_eq_of_lt <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg μ.hnFiltration.toFun (Nat.mod_eq_of_lt <| Nat.succ_lt_succ hi).symm

end Exists

section Unique

variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} [μ.ADCC] [μ.IsConvex]

omit [Nontrivial ℒ] [WellFoundedGT ℒ] [μ.ADCC] [μ.IsConvex] in
/-- Any semistable `RelSeries` from `⊥` to `⊤` with strictly decreasing `μ.A`-values underlies a
Harder–Narasimhan filtration, obtained by extending it constantly by `⊤`. -/
private lemma exists_hnFiltration_of_relSeries (s : RelSeries μ.semistableRel)
    (h : s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ i : ℕ, (hi : i + 1 < s.length) →
        ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
          μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩) :
    ∃ F : μ.HarderNarasimhanFiltration,
      ⇑F = (fun n ↦ if n ≤ s.length then s.toFun ↑n else ⊤) ∧ F.length = s.length := by
  have Fmono : ∀ i j : ℕ, i < j → j ≤ s.length → s.toFun ↑i < s.toFun ↑j :=
    fun _ _ hij hj ↦ relSeries_strictMono s (Fin.natCast_strictMono hj hij)
  refine ⟨{
      toFun := fun n ↦ if n ≤ s.length then s.toFun ↑n else ⊤
      length := s.length
      monotone := by
        refine monotone_nat_of_le_succ fun n ↦ ?_
        by_cases hn' : n + 1 ≤ s.length
        · simp only [Nat.le_of_succ_le hn', hn', ↓reduceIte]
          exact (Fmono n (n + 1) (lt_add_one n) hn').le
        · simp only [hn', ↓reduceIte, le_top]
      head_eq_bot := by
        simp only [zero_le, ↓reduceIte]
        exact h.1
      length_eq_top := by
        simp only [le_refl, ↓reduceIte, Fin.natCast_eq_last]
        exact h.2.1
      strictMonoOn := by
        intro i _ j hj hij
        rw [Set.mem_Iic] at hj
        simpa only [(hij.trans_le hj).le, hj, ↓reduceIte] using Fmono i j hij hj
      piecewise_isSemistable := by
        intro i hi
        convert (s.step ⟨i, hi⟩).choose_spec <;>
          simp only [hi.le, show i + 1 ≤ s.length from hi, ↓reduceIte,
            Fin.castSucc_mk, Fin.succ_mk, Fin.natCast_eq_mk (Nat.lt_add_right 1 hi),
            Fin.natCast_eq_mk (Nat.add_lt_add_right hi 1)]
      not_A_le_succ := by
        intro i hi
        convert h.2.2 i hi
        · simp only [(Nat.lt_of_succ_lt hi).le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [show i + 2 ≤ s.length from hi, ↓reduceIte] }, rfl, rfl⟩

/-- For a complete linearly ordered codomain, there is a unique finite series of semistable
intervals from `⊥` to `⊤` with strictly decreasing `μ.A`-values. -/
theorem existsUnique_relSeries_semistableRel (μ : PayoffFunction ℒ S)
    [μ.ADCC] [μ.IsConvex] :
    ∃! s : RelSeries μ.semistableRel,
      s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ i : ℕ, (hi : i + 1 < s.length) →
        ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
          μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩ := by
  apply existsUnique_of_exists_of_unique
  · exact exists_relSeries_semistableRel μ
  · intro F1 F2 h1 h2
    rcases exists_hnFiltration_of_relSeries F1 h1 with ⟨HN1, len1⟩
    rcases exists_hnFiltration_of_relSeries F2 h2 with ⟨HN2, len2⟩
    have h12 : HN1 = HN2 := (eq_hnFiltration HN1).trans (eq_hnFiltration HN2).symm
    have len_eq : F1.length = F2.length := by
      rw [← len1.2, ← len2.2, h12]
    ext x
    · rw [← len1.2, ← len2.2, h12]
    · simp only [Function.comp_apply]
      have hpointwise := congrFun
        (congrArg (DFunLike.coe (F := μ.HarderNarasimhanFiltration)) h12) (x : ℕ)
      rw [len1.1, len2.1] at hpointwise
      have hx1 : (x : ℕ) ≤ F1.length := Fin.is_le x
      have hx2 : (x : ℕ) ≤ F2.length := len_eq ▸ hx1
      convert hpointwise
      · simp only [Fin.cast_val_eq_self, hx1, ↓reduceIte]
      · simp only [hx2, ↓reduceIte]
        congr
        exact Fin.eq_of_val_eq (Fin.val_cast_of_lt (Nat.lt_add_one_of_le hx2)).symm

end Unique

end RelSeries

end PayoffFunction

end HarderNarasimhan
