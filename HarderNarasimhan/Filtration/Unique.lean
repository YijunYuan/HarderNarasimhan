/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Filtration.Exists

/-!
# Uniqueness of Harder–Narasimhan filtrations

Over a complete *linear* order `S`, the Harder–Narasimhan filtration of a payoff function is
unique: any filtration satisfying the axioms of
`PayoffFunction.HarderNarasimhanFiltration` coincides with the canonical construction
`μ.hnFiltration`.  This is the uniqueness half of the existence-and-uniqueness theorem for
Harder–Narasimhan filtrations and it is exposed as a `Unique` instance.

This file also repackages existence and uniqueness in terms of `RelSeries` for the relation
`μ.semistableRel`: a Harder–Narasimhan filtration is the same thing as a finite `RelSeries`
of semistable intervals from `⊥` to `⊤` whose successive `μ.A`-slopes strictly decrease.

## Main results

* `Unique (μ.HarderNarasimhanFiltration)` : over a complete linear order the
  Harder–Narasimhan filtration is unique.
* `PayoffFunction.exists_relSeries_semistableRel` : existence of a semistable `RelSeries`
  from `⊥` to `⊤` with strictly decreasing slopes.
* `PayoffFunction.existsUnique_relSeries_semistableRel` : its uniqueness over a complete
  linear order.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*}

section Unique

variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} [μ.ADCC] [μ.IsConvex]

open Classical in
/-- Any Harder–Narasimhan filtration coincides with the canonical one.  This is the
uniqueness half of the existence-and-uniqueness theorem; it is exposed through the `Unique`
instance below. -/
private theorem eq_hnFiltration (F : μ.HarderNarasimhanFiltration) : F = μ.hnFiltration := by
  have hμcvx : μ.IsConvexOn ⊤ := inferInstance
  have hfsi : ∀ i j : ℕ, i < j → j ≤ F.length → F i < F j :=
    fun i j hij hj ↦ F.strictMonoOn (hij.le.trans hj) hj hij
  have hbp : ∀ j : ℕ, (hj : j < F.length) →
      μ.IsBreakpoint ⟨F j, F (j + 1), hfsi j (j + 1) (lt_add_one j) hj⟩ (F (j + 1)) :=
    fun j hj ↦ (isBreakpoint_right_iff
      (I := ⟨F j, F (j + 1), hfsi j (j + 1) (lt_add_one j) hj⟩)).2 <|
      F.piecewise_isSemistable j hj
  have hmua : ∀ i j : ℕ, (hij : i < j) → (hj : j < F.length) →
      μ.A ⟨F i, F (i + 1), hfsi i (i + 1) (lt_add_one i) (by omega)⟩ >
      μ.A ⟨F j, F (j + 1), hfsi j (j + 1) (lt_add_one j) hj⟩ := by
    intro i
    have key : ∀ j : ℕ, (hij : i + 1 ≤ j) → (hj : j < F.length) →
        μ.A ⟨F i, F (i + 1), hfsi i (i + 1) (lt_add_one i) (by omega)⟩ >
        μ.A ⟨F j, F (j + 1), hfsi j (j + 1) (lt_add_one j) hj⟩ := by
      apply Nat.le_induction
      · exact fun hj ↦ lt_of_not_ge (F.not_A_le_succ i hj)
      · refine fun j hij hind hj ↦ gt_trans (hind (Nat.lt_of_succ_lt hj)) ?_
        exact lt_of_not_ge <| F.not_A_le_succ j hj
    exact fun j hij hj ↦ key j hij hj
  refine HarderNarasimhanFiltration.ext fun k ↦ ?_
  induction k with
  | zero => exact F.head_eq_bot.trans μ.hnFiltration.head_eq_bot.symm
  | succ n hn =>
    by_cases h₁ : n + 1 ≤ F.length
    · have h₂ : ∃ N : ℕ, N ≥ n + 1 ∧ μ.hnFiltration (n + 1) ≤ F N :=
        ⟨F.length, h₁, le_top.trans (F.eq_top_of_length_le le_rfl).ge⟩
      let i : ℕ := Nat.find h₂
      have h₃ : μ.hnFiltration n < μ.hnFiltration (n + 1) :=
        μ.hnFiltration.lt_succ_of_ne_top
          (hn ▸ F.ne_top_of_lt (lt_of_lt_of_le (lt_add_one n) h₁))
      have h₁₅ : i ≥ n + 1 := (Nat.find_spec h₂).1
      have h₉ : i > 0 := Nat.zero_lt_of_lt h₁₅
      have hile : i ≤ F.length := by
        by_contra! hc
        rcases not_and_or.1 (Nat.find_min h₂ hc) with c₁ | c₂
        · exact c₁ h₁
        · exact c₂ (le_top.trans (F.eq_top_of_length_le le_rfl).ge)
      have h₈ : i - 1 < F.length := Nat.sub_one_lt_of_le h₉ hile
      have h₄ : ¬ μ.hnFiltration (n + 1) ≤ F (i - 1) := by
        rcases not_and_or.1 (Nat.find_min h₂ (Nat.sub_one_lt h₉.ne')) with h₅ | h₅
        · rw [show i - 1 = n by omega, hn]
          exact not_le_of_gt h₃
        · exact h₅
      have h₁₃ : μ.hnFiltration n ≤ F (i - 1) := by
        rw [← hn]
        rcases (Nat.le_sub_one_of_lt h₁₅).eq_or_lt with h₁₄ | h₁₄
        · rw [h₁₄]
        · exact (hfsi n (i - 1) h₁₄ (by omega)).le
      have h₆ : μ.A ⟨μ.hnFiltration n, μ.hnFiltration (n + 1), h₃⟩ ≤
          μ.A ⟨F (i - 1), μ.hnFiltration (n + 1) ⊔ F (i - 1), right_lt_sup.2 h₄⟩ :=
        hμcvx.A_le_A_sup (StrictIntvl.mem_top (μ.hnFiltration (n + 1)))
          (StrictIntvl.mem_top (F (i - 1))) h₄ (le_inf (le_of_lt h₃) h₁₃)
      have h₇ : F (i - 1) < F i := hfsi (i - 1) i (Nat.sub_one_lt h₉.ne') hile
      have h₁₀ : μ.A ⟨μ.hnFiltration n, μ.hnFiltration (n + 1), h₃⟩ ≤
          μ.A ⟨F (i - 1), F i, h₇⟩ := by
        have h₁₁ := hbp (i - 1) h₈
        simp only [Nat.sub_one_add_one h₉.ne'] at h₁₁
        exact le_trans h₆ <| le_of_not_gt (h₁₁.not_lt (μ.hnFiltration (n + 1) ⊔ F (i - 1))
          ⟨le_sup_right, sup_le_iff.2 ⟨(Nat.find_spec h₂).2, le_of_lt h₇⟩⟩
          <| ne_of_lt <| right_lt_sup.2 h₄)
      have hspec := mem_breakpoints.1
        (hnFiltration_succ_isGreatest_breakpoints (ne_of_lt (lt_of_lt_of_le h₃ le_top))).1
      have h₁₂ : i = n + 1 := by
        refine eq_of_le_of_not_lt' h₁₅ ?_
        by_contra! hlt
        have hlt' : μ.hnFiltration n < F (n + 1) :=
          hn.ge.trans_lt (hfsi n (n + 1) (lt_add_one n) h₁)
        have h₁₃' := hmua n (i - 1) (Nat.lt_sub_of_add_lt hlt) h₈
        simp only [hn, Nat.sub_one_add_one h₉.ne', gt_iff_lt] at h₁₃'
        exact hspec.not_lt (F (n + 1)) ⟨le_of_lt hlt', le_top⟩ (ne_of_lt hlt')
          (lt_of_le_of_lt h₁₀ h₁₃')
      have h₁₄ := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg (⇑F) h₁₂)
      have h₁₉ : μ.hnFiltration n < F (n + 1) := lt_of_lt_of_le h₃ h₁₄
      have h₁₆ : F n < μ.hnFiltration (n + 1) := hn.le.trans_lt h₃
      have h₁₇ := le_of_not_gt <| (hbp n h₁).not_lt (μ.hnFiltration (n + 1))
        ⟨le_of_lt h₁₆, h₁₄⟩ <| ne_of_lt h₁₆
      simp only [hn] at h₁₇
      exact eq_of_le_of_ge (hspec.le_of_eq (F (n + 1)) ⟨le_of_lt h₁₉, le_top⟩ (ne_of_lt h₁₉)
        (eq_of_le_of_not_lt h₁₇ <| hspec.not_lt (F (n + 1)) ⟨le_of_lt h₁₉, le_top⟩ <|
          ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [F.eq_top_of_length_le (Nat.le_of_succ_le h₁), eq_comm]
      rw [F.eq_top_of_length_le (Nat.le_of_lt_succ h₁)] at hn
      have h₀ : ¬ n < μ.hnFiltration.length :=
        (HarderNarasimhanFiltration.ne_top_iff_lt_length (F := μ.hnFiltration)).not.1
          (not_ne_iff.2 hn.symm)
      exact not_ne_iff.1 <|
        (HarderNarasimhanFiltration.ne_top_iff_lt_length (F := μ.hnFiltration)).not.2
          (by omega)

/-- Over a complete linear order the Harder–Narasimhan filtration is unique; the canonical
representative is `μ.hnFiltration`. -/
noncomputable instance : Unique (μ.HarderNarasimhanFiltration) where
  uniq := eq_hnFiltration

end Unique

section RelSeries

open Fin.NatCast

section Exists

variable [CompleteLattice S]

/-- Existence of a `RelSeries` of semistable intervals from `⊥` to `⊤` with strictly
decreasing `μ.A`-slopes: the `RelSeries` repackaging of the canonical Harder–Narasimhan
filtration `μ.hnFiltration`. -/
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
/-- Any semistable `RelSeries` from `⊥` to `⊤` with strictly decreasing slopes underlies a
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
        have e₁ : (if i ≤ s.length then s.toFun ↑i else ⊤) = s.toFun (Fin.castSucc ⟨i, hi⟩) := by
          simp only [hi.le, ↓reduceIte, Fin.castSucc_mk,
            Fin.natCast_eq_mk (Nat.lt_add_right 1 hi)]
        have e₂ : (if i + 1 ≤ s.length then s.toFun ↑(i + 1) else ⊤) =
            s.toFun (Fin.succ ⟨i, hi⟩) := by
          simp only [show i + 1 ≤ s.length from hi, ↓reduceIte, Fin.succ_mk,
            Fin.natCast_eq_mk (Nat.add_lt_add_right hi 1)]
        have hIJ : (⟨s.toFun (Fin.castSucc ⟨i, hi⟩), s.toFun (Fin.succ ⟨i, hi⟩),
            (s.step ⟨i, hi⟩).choose⟩ : StrictIntvl ℒ) =
              ⟨if i ≤ s.length then s.toFun ↑i else ⊤,
                if i + 1 ≤ s.length then s.toFun ↑(i + 1) else ⊤,
                by rw [e₁, e₂]; exact (s.step ⟨i, hi⟩).choose⟩ :=
          StrictIntvl.ext e₁.symm e₂.symm
        exact hIJ ▸ (s.step ⟨i, hi⟩).choose_spec
      not_A_le_succ := by
        intro i hi
        convert h.2.2 i hi
        · simp only [(Nat.lt_of_succ_lt hi).le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [show i + 2 ≤ s.length from hi, ↓reduceIte] }, rfl, rfl⟩

/-- Over a complete linear order, there is a *unique* `RelSeries` of semistable intervals
from `⊥` to `⊤` with strictly decreasing `μ.A`-slopes: the `RelSeries` repackaging of the
uniqueness of the Harder–Narasimhan filtration. -/
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
      have hx2 := congrFun (congrArg (DFunLike.coe (F := μ.HarderNarasimhanFiltration)) h12)
        (x : ℕ)
      rw [len1.1, len2.1] at hx2
      convert hx2
      · simp only [Fin.cast_val_eq_self]
        if hx : (x : ℕ) ≤ F1.length then
          simp only [hx, ↓reduceIte]
        else
          simp only [hx, ↓reduceIte]
          simp only [not_le] at hx
          have := Fin.is_le x
          exfalso
          linarith
      · if hx : (x : ℕ) ≤ F2.length then
          simp only [hx, ↓reduceIte]
          congr
          refine Fin.eq_of_val_eq <| Eq.symm (Fin.val_cast_of_lt ?_)
          exact Nat.lt_add_one_of_le hx
        else
          simp only [hx, ↓reduceIte]
          simp only [not_le] at hx
          have : (x : ℕ) ≤ F2.length := len_eq ▸ Fin.is_le x
          exfalso
          linarith

end Unique

end RelSeries

end PayoffFunction

end HarderNarasimhan
