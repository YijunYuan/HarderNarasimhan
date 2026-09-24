/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Defs
public import HarderNarasimhan.Semistability.Results

/-!
# Section 3.3: implementation of Harder–Narasimhan filtrations

The current greatest-breakpoint construction proves Definition 3.9; the uniqueness proof
implements Theorem 3.10. The final conversion lemmas retain the relation-series API.
-/

@[expose] public section

open HarderNarasimhan.PayoffFunction

namespace HarderNarasimhan.Impl

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hwf : WellFoundedGT ℒ]
variable {S : Type*} [CompleteLattice S]
variable (μ : PayoffFunction ℒ S) [μ.ADCC] [μ.IsConvex] [hadm : μ.Admissible]

open Classical in
/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
The chain starting at `⊥` whose successor terms are greatest breakpoints of the remaining
intervals. It is constant once it reaches `⊤`. -/
private noncomputable def HNFil (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev := HNFil n
    if htop : prev = ⊤ then
      ⊤
    else
      (exists_isGreatest_breakpoints (I := ⟨prev, ⊤, lt_top_iff_ne_top.2 htop⟩)
        ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
        (hadm.total_or_attained.imp id fun h z hzI hz ↦
          h ⟨prev, z, lt_of_le_of_ne hzI.left hz⟩)).choose

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
Each term following a term below `⊤` is the greatest breakpoint of the remaining interval. -/
private lemma HNFil_isGreatest (n : ℕ) (h' : HNFil μ n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨HNFil μ n, ⊤, h'.lt_top⟩) (HNFil μ (n + 1)) := by
  simp only [HNFil, h']
  exact (exists_isGreatest_breakpoints (I := ⟨HNFil μ n, ⊤, h'.lt_top⟩)
    ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
    (hadm.total_or_attained.imp id fun h z hzI hz ↦
      h ⟨HNFil μ n, z, lt_of_le_of_ne hzI.left hz⟩)).choose_spec

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
Each term below `⊤` is strictly less than its successor. -/
private lemma HNFil_lt_succ (n : ℕ) (hn : HNFil μ n ≠ ⊤) : HNFil μ n < HNFil μ (n + 1) :=
  lt_of_le_of_ne (HNFil_isGreatest μ n hn).1.1.1 (HNFil_isGreatest μ n hn).1.2

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
`HNFil` reaches `⊤` in finite time, by well-foundedness of `>`. -/
private lemma HNFil_exists_eq_top : ∃ N : ℕ, HNFil μ N = ⊤ := by
  by_contra!
  exact (wellFounded_iff_isEmpty_descending_chain.1 hwf.wf).elim
    ⟨fun n ↦ HNFil μ n, fun n ↦ HNFil_lt_succ μ n (this n)⟩

open Classical in
/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
The least index at which `HNFil` reaches `⊤`. -/
private noncomputable def HNlen : ℕ := Nat.find (HNFil_exists_eq_top μ)

open Classical in
/-- Auxiliary lemma for Definition 3.9. The chain reaches the top exactly at its stopping index. -/
private lemma HNFil_ne_top_iff (n : ℕ) : HNFil μ n ≠ ⊤ ↔ n < HNlen μ := by
  refine ⟨fun hn ↦ ?_, Nat.find_min (HNFil_exists_eq_top μ)⟩
  by_contra!
  exact hn (Nat.le_induction (Nat.find_spec (HNFil_exists_eq_top μ))
    (fun k _ hk' ↦ by simp only [HNFil, hk', ↓reduceDIte]) n this)

/-- Auxiliary lemma for Definition 3.9.
The chain is strictly increasing through its stopping index. -/
private lemma HNFil_strictMonoOn : StrictMonoOn (HNFil μ) (Set.Iic (HNlen μ)) := by
  intro i _ j hj hij
  revert hj
  induction j, hij using Nat.le_induction with
  | base =>
    intro hj
    exact HNFil_lt_succ μ i ((HNFil_ne_top_iff μ i).2 hj)
  | succ j hij ih =>
    intro hj
    exact (ih (Nat.le_of_succ_le hj)).trans (HNFil_lt_succ μ j ((HNFil_ne_top_iff μ j).2 hj))

/-- Auxiliary lemma for Definition 3.9. The stopping index has value top. -/
private lemma HNFil_length_eq_top : HNFil μ (HNlen μ) = ⊤ := by
  classical
  exact Nat.find_spec (HNFil_exists_eq_top μ)

/-- Auxiliary lemma for Definition 3.9. The chain is monotone, including its constant tail. -/
private lemma HNFil_monotone : Monotone (HNFil μ) := by
  have htop : ∀ n : ℕ, HNlen μ ≤ n → HNFil μ n = ⊤ :=
    Nat.le_induction (HNFil_length_eq_top μ)
      fun k _ hk' ↦ by simp only [HNFil, hk', ↓reduceDIte]
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · by_cases hj : j ≤ HNlen μ
    · exact (HNFil_strictMonoOn μ (hlt.le.trans hj) hj hlt).le
    · exact (htop j (not_le.1 hj).le) ▸ le_top

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
Each step of the chain before it reaches `⊤` is semistable. -/
private lemma HNFil_piecewise_isSemistable :
    ∀ i : ℕ, (hi : i < HNlen μ) →
      (μ.restrict ⟨HNFil μ i, HNFil μ (i + 1),
        HNFil_strictMonoOn μ hi.le hi (lt_add_one i)⟩).IsSemistable :=
  fun i hi ↦ IsBreakpoint.isSemistable_restrict (mem_breakpoints.1
    (HNFil_isGreatest μ i ((HNFil_ne_top_iff μ i).2 hi)).1)

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
No `μ.A`-value of a step is less than or equal to that of the next step. -/
private lemma HNFil_not_A_le_succ :
    ∀ i : ℕ, (hi : i + 1 < HNlen μ) →
      ¬ μ.A ⟨HNFil μ i, HNFil μ (i + 1),
          HNFil_lt_succ μ i ((HNFil_ne_top_iff μ i).2 (Nat.lt_of_succ_lt hi))⟩ ≤
        μ.A ⟨HNFil μ (i + 1), HNFil μ (i + 2),
          HNFil_lt_succ μ (i + 1) ((HNFil_ne_top_iff μ (i + 1)).2 hi)⟩ := by
  intro i hj
  have hi : HNFil μ i ≠ ⊤ := (HNFil_ne_top_iff μ i).2 (lt_trans (lt_add_one i) hj)
  have hi' : HNFil μ (i + 1) < HNFil μ (i + 1 + 1) :=
    HNFil_lt_succ μ (i + 1) ((HNFil_ne_top_iff μ (i + 1)).2 hj)
  exact IsBreakpoint.not_A_le (mem_breakpoints.1 (HNFil_isGreatest μ i hi).1)
    ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
    ⟨(lt_trans (HNFil_lt_succ μ i hi) hi').le, le_top⟩ hi'

/-- Definition 3.9: the canonical Harder–Narasimhan filtration.
The Harder–Narasimhan filtration obtained by starting at `⊥` and successively taking the
greatest breakpoint of the remaining interval.

Use `HarderNarasimhan.Impl.PayoffFunction.hnFiltration_succ_isGreatest_breakpoints` for the
successor terms. For a complete linearly ordered codomain, this is the unique
Harder–Narasimhan filtration; see `HarderNarasimhan/Filtration/Results.lean`. -/
@[no_expose]
noncomputable def hnFiltration : μ.HarderNarasimhanFiltration where
  toFun := HNFil μ
  length := HNlen μ
  monotone := HNFil_monotone μ
  head_eq_bot := rfl
  length_eq_top := HNFil_length_eq_top μ
  strictMonoOn := HNFil_strictMonoOn μ
  piecewise_isSemistable := HNFil_piecewise_isSemistable μ
  not_A_le_succ := HNFil_not_A_le_succ μ

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
The canonical filtration provides a default Harder–Narasimhan filtration. -/
noncomputable instance : Inhabited (μ.HarderNarasimhanFiltration) := ⟨(hnFiltration μ)⟩

variable {μ}

/-- Auxiliary construction for Definition 3.9 and Theorem 3.10.
Each term of the canonical filtration following a term below `⊤` is the greatest
breakpoint of the interval between that term and `⊤`. -/
lemma hnFiltration_succ_isGreatest_breakpoints {n : ℕ} (h : (hnFiltration μ) n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨(hnFiltration μ) n, ⊤, h.lt_top⟩) ((hnFiltration μ) (n + 1)) :=
  HNFil_isGreatest μ n h

/-- Definition 3.9 (last displayed equality), also used in Remark 3.16.
Replacing the left endpoint `⊥` by a term of the canonical filtration preserves `μ.A`,
provided that the right endpoint lies strictly above that term. -/
theorem hnFiltration_A_bot_eq_A {n : ℕ} {y : ℒ} (hy : (hnFiltration μ) n < y) :
    μ.A ⟨⊥, y, bot_le.trans_lt hy⟩ = μ.A ⟨(hnFiltration μ) n, y, hy⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev_lt : (hnFiltration μ) n < y :=
      lt_of_le_of_lt (((hnFiltration μ)).monotone (Nat.le_succ n)) hy
    have hne : (hnFiltration μ) n ≠ ⊤ := (hprev_lt.trans_le le_top).ne
    have hbreakpoint := mem_breakpoints.1
      (hnFiltration_succ_isGreatest_breakpoints (μ := μ) hne).1
    calc
      _ = μ.A ⟨(hnFiltration μ) n, y, hprev_lt⟩ := ih hprev_lt
      _ = _ := IsBreakpoint.A_eq_A_of_lt hbreakpoint ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
        (hadm.total_or_attained.imp id fun h z hzI hz ↦
          h ⟨(hnFiltration μ) n, z, lt_of_le_of_ne hzI.left hz⟩)
        ⟨hprev_lt.le, le_top⟩ hy

end PayoffFunction

end HarderNarasimhan.Impl

namespace HarderNarasimhan.Impl

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*}

section Unique

variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} [μ.ADCC] [μ.IsConvex]

open Classical in
/-- Auxiliary implementation of Theorem 3.10.
Every Harder–Narasimhan filtration equals the filtration obtained by taking greatest
breakpoints. -/
private theorem eq_hnFiltration (F : μ.HarderNarasimhanFiltration) : F = (hnFiltration μ) := by
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
  | zero => exact F.head_eq_bot.trans (hnFiltration μ).head_eq_bot.symm
  | succ n hn =>
    by_cases hnext : n + 1 ≤ F.length
    · -- Find the first step of F containing the next canonical breakpoint.
      have hcover : ∃ N : ℕ, N ≥ n + 1 ∧ (hnFiltration μ) (n + 1) ≤ F N :=
        ⟨F.length, hnext, le_top.trans (F.eq_top_of_length_le le_rfl).ge⟩
      let i : ℕ := Nat.find hcover
      obtain ⟨hn_le_i, hcanonical_le⟩ : n + 1 ≤ i ∧ (hnFiltration μ) (n + 1) ≤ F i :=
        Nat.find_spec hcover
      have hi_pos : 0 < i := Nat.zero_lt_of_lt hn_le_i
      have hi_length : i ≤ F.length :=
        Nat.find_min' hcover ⟨hnext, le_top.trans (F.eq_top_of_length_le le_rfl).ge⟩
      have hprev_length : i - 1 < F.length := Nat.sub_one_lt_of_le hi_pos hi_length
      have hcanonical_growth : (hnFiltration μ) n < (hnFiltration μ) (n + 1) :=
        (hnFiltration μ).lt_succ_of_ne_top
          (hn ▸ F.ne_top_of_lt (lt_of_lt_of_le (lt_add_one n) hnext))
      have hnot_le_prev : ¬ (hnFiltration μ) (n + 1) ≤ F (i - 1) := by
        rcases not_and_or.1 (Nat.find_min hcover (Nat.sub_one_lt hi_pos.ne')) with hindex | hvalue
        · rw [show i - 1 = n by omega, hn]
          exact not_le_of_gt hcanonical_growth
        · exact hvalue
      have hbase_le_prev : (hnFiltration μ) n ≤ F (i - 1) := by
        rw [← hn]
        exact F.monotone (Nat.le_sub_one_of_lt hn_le_i)
      have hstep_lt : F (i - 1) < F i :=
        strict_growth (i - 1) i (Nat.sub_one_lt hi_pos.ne') hi_length
      -- Convexity and semistability compare the canonical slope with this step's slope.
      have hslope_le : μ.A ⟨(hnFiltration μ) n, (hnFiltration μ) (n + 1), hcanonical_growth⟩ ≤
          μ.A ⟨F (i - 1), F i, hstep_lt⟩ := by
        have hprev_breakpoint := step_breakpoint (i - 1) hprev_length
        simp only [Nat.sub_one_add_one hi_pos.ne'] at hprev_breakpoint
        calc
          _ ≤ μ.A ⟨F (i - 1), (hnFiltration μ) (n + 1) ⊔ F (i - 1),
              right_lt_sup.2 hnot_le_prev⟩ :=
            IsConvexOn.A_le_A_sup hμcvx (StrictIntvl.mem_top ((hnFiltration μ) (n + 1)))
              (StrictIntvl.mem_top (F (i - 1))) hnot_le_prev
              (le_inf hcanonical_growth.le hbase_le_prev)
          _ ≤ _ := le_of_not_gt (hprev_breakpoint.not_lt
            ((hnFiltration μ) (n + 1) ⊔ F (i - 1))
            ⟨le_sup_right, sup_le hcanonical_le hstep_lt.le⟩
            (ne_of_lt (right_lt_sup.2 hnot_le_prev)))
      have hcanonical_breakpoint := mem_breakpoints.1
        (hnFiltration_succ_isGreatest_breakpoints (hcanonical_growth.trans_le le_top).ne).1
      have hi_eq : i = n + 1 := by
        refine eq_of_le_of_not_lt' hn_le_i ?_
        by_contra! hlt
        have hnext_lt : (hnFiltration μ) n < F (n + 1) :=
          hn.ge.trans_lt (strict_growth n (n + 1) (lt_add_one n) hnext)
        have hslope_lt := slopes_strictAnti n (i - 1) (Nat.lt_sub_of_add_lt hlt) hprev_length
        simp only [hn, Nat.sub_one_add_one hi_pos.ne', gt_iff_lt] at hslope_lt
        exact hcanonical_breakpoint.not_lt (F (n + 1)) ⟨hnext_lt.le, le_top⟩ hnext_lt.ne
          (hslope_le.trans_lt hslope_lt)
      rw [hi_eq] at hcanonical_le
      have hnext_lt : (hnFiltration μ) n < F (n + 1) := hcanonical_growth.trans_le hcanonical_le
      -- Both endpoints maximise the same value; the canonical breakpoint is greatest.
      refine le_antisymm (hcanonical_breakpoint.le_of_eq (F (n + 1))
        ⟨hnext_lt.le, le_top⟩ hnext_lt.ne ?_) hcanonical_le
      symm
      refine eq_of_le_of_not_lt ?_
        (hcanonical_breakpoint.not_lt (F (n + 1)) ⟨hnext_lt.le, le_top⟩ hnext_lt.ne)
      simpa only [hn] using le_of_not_gt ((step_breakpoint n hnext).not_lt
        ((hnFiltration μ) (n + 1)) ⟨(hn.le.trans_lt hcanonical_growth).le, hcanonical_le⟩
        (hn.le.trans_lt hcanonical_growth).ne)
    · have hn_top : (hnFiltration μ) n = ⊤ :=
        hn.symm.trans (F.eq_top_of_length_le (by omega))
      rw [F.eq_top_of_length_le (by omega)]
      exact ((hnFiltration μ).eq_top_of_length_le
        (((hnFiltration μ).length_le_of_eq_top hn_top).trans (Nat.le_succ n))).symm

/-- Auxiliary implementation of Theorem 3.10.
Over a complete linear order the Harder–Narasimhan filtration is unique; the canonical
representative is `(hnFiltration μ)`. -/
@[no_expose]
noncomputable instance : Unique (μ.HarderNarasimhanFiltration) where
  uniq := eq_hnFiltration

end Unique

section RelSeries

open Fin.NatCast

section Exists

variable [CompleteLattice S]

/-- Definition 3.9, expressed as a finite relation series.
There is a finite series of semistable intervals from `⊥` to `⊤` whose successive
`μ.A`-values satisfy `¬ aᵢ ≤ aᵢ₊₁`. -/
theorem exists_relSeries_semistableRel (μ : PayoffFunction ℒ S)
    [μ.ADCC] [μ.IsConvex] [μ.Admissible] :
    ∃ s : RelSeries μ.semistableRel,
      s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ i : ℕ, (hi : i + 1 < s.length) →
        ¬ μ.A ⟨s.toFun ↑i, s.toFun ↑(i + 1), relSeries_step_lt s hi⟩ ≤
          μ.A ⟨s.toFun ↑(i + 1), s.toFun ↑(i + 2), relSeries_succ_step_lt s hi⟩ := by
  refine ⟨{ toFun := fun n ↦ (hnFiltration μ) n
            length := (hnFiltration μ).length
            step := fun i ↦
              ⟨(hnFiltration μ).strictMonoOn ((Nat.lt_add_one i.val).le.trans (Fin.is_le i.succ))
                  (Fin.is_le i.succ) (Nat.lt_add_one i.val),
                (hnFiltration μ).piecewise_isSemistable i.val i.prop⟩ },
    (hnFiltration μ).head_eq_bot, (hnFiltration μ).length_eq_top, ?_⟩
  refine fun i hi hc ↦ (hnFiltration μ).not_A_le_succ i hi ?_
  convert hc
  · exact congrArg (hnFiltration μ).toFun (Nat.mod_eq_of_lt <| lt_trans (Nat.lt_add_one i) <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg (hnFiltration μ).toFun (Nat.mod_eq_of_lt <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg (hnFiltration μ).toFun (Nat.mod_eq_of_lt <|
      lt_trans hi (Nat.lt_add_one _)).symm
  · exact congrArg (hnFiltration μ).toFun (Nat.mod_eq_of_lt <| Nat.succ_lt_succ hi).symm

end Exists

section Unique

variable [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} [μ.ADCC] [μ.IsConvex]

omit [Nontrivial ℒ] [WellFoundedGT ℒ] [μ.ADCC] [μ.IsConvex] in
/-- Auxiliary implementation of Theorem 3.10.
Any semistable `RelSeries` from `⊥` to `⊤` with strictly decreasing `μ.A`-values underlies a
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

/-- Theorem 3.10, expressed as existence and uniqueness of a finite relation series.
For a complete linearly ordered codomain, there is a unique finite series of semistable
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

end HarderNarasimhan.Impl
