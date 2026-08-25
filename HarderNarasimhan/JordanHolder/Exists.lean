/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolder.Defs
public import Mathlib.Order.RelSeries

/-!
# Existence of Jordan–Hölder filtrations

This file constructs a Jordan–Hölder filtration of a semistable slope-like payoff function
`μ` on a well-founded bounded lattice, under the standing hypotheses
`μ.FiniteTotalPayoff` (nondegeneracy) and `μ.EventuallyTopDCC` (termination).

The construction is greedy: starting from `⊤`, as long as the current term is not `⊥`, the
next term is a minimal element among the points `p` strictly between `⊥` and the current
term with `μ (⊥, p) = μ ⊤`.  Semistability and the seesaw property show that each step
carries the total payoff and that minimality forces stability of the steps; the chain
condition `μ.EventuallyTopDCC` forces the chain to reach `⊥` after finitely many steps.
The existence result is exposed as a `Nonempty` instance (in contrast to the
Harder–Narasimhan filtration, a Jordan–Hölder filtration is not unique, so there is no
canonical choice).

## Main results

* `Nonempty (μ.JordanHolderFiltration)` : Jordan–Hölder filtrations exist.
* `PayoffFunction.exists_relSeries_jordanHolderRel` : the `RelSeries` repackaging; a finite
  chain for `μ.jordanHolderRel` from `⊤` to `⊥` exists.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)

omit [CompleteLinearOrder S] in
open Classical in
/-- The greedy chain underlying a Jordan–Hölder filtration.  At step `k + 1`, choose a
minimal element among the points `p` strictly between `⊥` and the previous term with
`μ (⊥, p) = μ ⊤`, falling back to `⊥` when there is none. -/
private noncomputable def JHFil (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil n ∧ μ ⟨⊥, p, h⟩ = μ ⊤}
    if h𝒮 : 𝒮.Nonempty then
      (hacc.wf.has_min 𝒮 h𝒮).choose
    else
      ⊥

omit [CompleteLinearOrder S] in
/-- One-step strict decrease of `JHFil` above `⊥`, from minimality of the chosen element. -/
private lemma JHFil_anti_mono :
    ∀ k : ℕ, JHFil μ k > ⊥ → JHFil μ k > JHFil μ (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simpa only [h]

omit [CompleteLinearOrder S] in
/-- The chain `JHFil` is antitone: it decreases strictly until it reaches `⊥` and is
constantly `⊥` afterwards. -/
private lemma JHFil_antitone : Antitone (JHFil μ) :=
  antitone_nat_of_succ_le fun n ↦ by
    by_cases h : JHFil μ n = ⊥
    · refine le_of_eq_of_le ?_ bot_le
      have hempty : ¬ {p : ℒ | ∃ hp : ⊥ < p, p < JHFil μ n ∧ μ ⟨⊥, p, hp⟩ = μ ⊤}.Nonempty := by
        rintro ⟨p, -, hlt, -⟩
        exact not_lt_bot (h ▸ hlt)
      simp only [JHFil]
      exact dif_neg hempty
    · exact (JHFil_anti_mono μ n <| bot_lt_iff_ne_bot.2 h).le

variable [hsl : μ.IsSlopeLike]

open Classical in
/-- Each step of `JHFil` above `⊥` carries the total payoff `μ ⊤`, by the seesaw property
and the defining choice of the next term. -/
private lemma JHFil_step_payoff_eq_tot :
    ∀ k : ℕ, (hk : JHFil μ k > ⊥) →
      μ ⟨JHFil μ (k + 1), JHFil μ k, JHFil_anti_mono μ k hk⟩ = μ ⊤ := by
  intro k
  induction k with
  | zero =>
    intro hk'
    simp only [JHFil]
    by_cases this : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
    · simp only [this, ↓reduceDIte]
      let minTop := hacc.wf.has_min _ this
      have this' := minTop.choose_spec.1.2.2
      exact ((Or.resolve_left <| (Or.resolve_left <|
        hsl.seesaw minTop.choose_spec.1.choose minTop.choose_spec.1.out.choose_spec.1)
        (by aesop)) (by aesop)).2.symm
    · simp only [this, ↓reduceDIte]
      rfl
  | succ k hk =>
    intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ =
        μ ⊤}.Nonempty := by
      by_contra!
      simp only [JHFil, this, Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt,
        lt_self_iff_false] at hk'
    let min1 := hacc.wf.has_min _ jh_kp1_ntop
    have jh_kp1_ntop' : JHFil μ k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil, jh_kp1_ntop]
      exact min1.choose_spec.1.out.choose_spec.1
    have bot_jh_kp1_eq_ans := min1.choose_spec.1.2.2
    by_cases jh_kp2_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ (k + 1) ∧ μ ⟨⊥, p, h⟩
        = μ ⊤}.Nonempty
    · let min2 := hacc.wf.has_min _ jh_kp2_ntop
      have smart : μ ⟨⊥, min2.choose, min2.choose_spec.1.out.1⟩ =
          μ ⟨⊥, JHFil μ (k + 1), hk'⟩ := by
        rw [min2.choose_spec.1.out.choose_spec.2, ← bot_jh_kp1_eq_ans]
        simp only [JHFil, jh_kp1_ntop]
        simp only [exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte]
      have hfinal : μ ⟨⊥, JHFil μ (k + 1), hk'⟩ =
          μ ⟨min2.choose, JHFil μ (k + 1),
            min2.choose_spec.1.out.choose_spec.1⟩ := by
        refine (Or.resolve_left ((Or.resolve_left <|
          hsl.seesaw min2.choose_spec.1.out.choose min2.choose_spec.1.out.choose_spec.1)
          (?_)) (?_)).2
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]
          simp only [JHFil, jh_kp1_ntop]
          simp only [↓reduceDIte,
            exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
            lt_self_iff_false, not_false_eq_true]
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]
          simp only [JHFil, jh_kp1_ntop]
          simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
            forall_exists_index, lt_self_iff_false, not_false_eq_true]
      conv_lhs =>
        arg 2; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, gt_iff_lt, and_imp,
          forall_exists_index]
      simp only [exists_and_left, Set.mem_ofPred_eq, and_imp,
        forall_exists_index] at hfinal
      rw [← hfinal]
      simp only [JHFil, jh_kp1_ntop]
      simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
        forall_exists_index]
      simp only [exists_and_left, Set.mem_ofPred_eq, and_imp,
        forall_exists_index] at bot_jh_kp1_eq_ans
      exact bot_jh_kp1_eq_ans
    · conv_lhs =>
        arg 2; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp only [↓reduceDIte]
      have this' : μ ⟨⊥, JHFil μ k, jh_kp1_ntop'⟩ = μ ⊤ := by
        by_cases hh : k = 0
        · simp only [hh, JHFil]
          rfl
        · have : JHFil μ k = JHFil μ ((k - 1) + 1) := by
            simp only [Nat.sub_one_add_one hh]
          simp only [this]
          have : {p | ∃ (h : ⊥ < p), p < JHFil μ (k - 1) ∧ μ ⟨⊥, p, h⟩ =
              μ ⊤}.Nonempty := by
            by_contra hthis
            rw [this] at jh_kp1_ntop'
            simp only [JHFil, hthis] at jh_kp1_ntop'
            simp only [↓reduceDIte, gt_iff_lt, lt_self_iff_false] at jh_kp1_ntop'
          simp only [JHFil, this]
          simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
            forall_exists_index]
          simpa only [exists_and_left, Set.mem_ofPred_eq, gt_iff_lt, and_imp,
            forall_exists_index] using (hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.2
      simp only [← this']
      have : JHFil μ (k + 1) < JHFil μ k := by
        simpa only [JHFil, jh_kp1_ntop, ↓reduceDIte] using
          min1.choose_spec.1.out.choose_spec.1
      have this'' : μ ⟨⊥, JHFil μ (k + 1), hk'⟩ =
          μ ⟨JHFil μ (k + 1), JHFil μ k, this⟩ := by
        rw [hk jh_kp1_ntop', ← bot_jh_kp1_eq_ans]
        simp only [JHFil, jh_kp1_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
          forall_exists_index]
      exact ((Or.resolve_left <| (Or.resolve_left <| hsl.seesaw hk' this)
        (fun this_1 ↦ ne_of_lt
        (lt_trans this_1.left this_1.right) this'')) (fun this_1 ↦ ne_of_lt
        (gt_trans this_1.1 this_1.2) (Eq.symm this''))).1

variable [hftp : μ.FiniteTotalPayoff] [hdc : μ.EventuallyTopDCC]

/-- The chain `JHFil` reaches `⊥` in finitely many steps: otherwise `μ.EventuallyTopDCC`
would produce a step of payoff `⊤`, contradicting `μ.FiniteTotalPayoff` via
`JHFil_step_payoff_eq_tot`. -/
private lemma JHFil_fin_len : ∃ N : ℕ, JHFil μ N = ⊥ := by
  by_contra! hc
  rcases hdc.exists_eq_top (fun n ↦ JHFil μ n) (strictAnti_nat_of_succ_lt <|
    fun n ↦ JHFil_anti_mono μ n (bot_lt_iff_ne_bot.2 <| hc n)) with ⟨N, hN⟩
  exact hftp.ne_top.symm <| hN ▸
    JHFil_step_payoff_eq_tot μ N (bot_lt_iff_ne_bot.2 <| hc N)

open Classical in
/-- The least index at which `JHFil` reaches `⊥`. -/
private noncomputable def JHlen : ℕ := Nat.find (JHFil_fin_len μ)

open Classical in
private lemma JHFil_bot_lt {n : ℕ} (hn : n < JHlen μ) : ⊥ < JHFil μ n :=
  bot_lt_iff_ne_bot.2 (Nat.find_min (JHFil_fin_len μ) hn)

open Classical in
private lemma JHFil_length_eq_bot : JHFil μ (JHlen μ) = ⊥ := Nat.find_spec (JHFil_fin_len μ)

private lemma JHFil_strictAntiOn : StrictAntiOn (JHFil μ) (Set.Iic (JHlen μ)) :=
  fun x _ _y hy hxy ↦ lt_of_le_of_lt (JHFil_antitone μ hxy)
    (JHFil_anti_mono μ x (JHFil_bot_lt μ (lt_of_lt_of_le hxy hy)))

variable [hst : μ.IsSemistable]

omit hftp in
open Classical in
/-- Stability of the steps of `JHFil`: refining a step through a strictly intermediate
point strictly decreases the payoff, by minimality of the chosen next term. -/
private lemma JHFil_refine_lt_step_payoff :
    ∀ k : ℕ, (hk : JHFil μ k > ⊥) → ∀ z : ℒ, (h' : JHFil μ (k + 1) < z) →
      (h'' : z < JHFil μ k) →
      μ ⟨JHFil μ (k + 1), z, h'⟩ <
        μ ⟨JHFil μ (k + 1), JHFil μ k, JHFil_anti_mono μ k hk⟩ := by
  intro k hk z h' h''
  have this_new : μ.max ⊤ = μ ⊤ :=
    max_top_eq_apply_iff.2
      (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
  have this_q : μ ⟨⊥, z, lt_of_le_of_lt bot_le h'⟩ ≤ μ ⊤ :=
    this_new ▸ le_iSup₂_of_le z ⟨lt_of_le_of_lt bot_le h', le_top⟩ le_rfl
  by_cases hfp1bot : JHFil μ (k + 1) = ⊥
  · simp only [hfp1bot]
    have : ¬ {p | ∃ (h : ⊥ < p), p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ =
        μ ⊤}.Nonempty := by
      by_contra!
      simp only [JHFil, this] at hfp1bot
      have := (hacc.wf.has_min _ this).choose_spec.1.out.choose
      simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
        forall_exists_index] at hfp1bot
      simp only [exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index] at this
      exact (ne_of_lt this) hfp1bot.symm
    replace this := Set.eq_empty_iff_forall_notMem.1 (Set.not_nonempty_iff_eq_empty.1 this) z
    simp only [exists_and_left, Set.mem_ofPred_eq, not_and, not_exists] at this
    replace := lt_of_le_of_ne this_q <| this h'' (lt_of_le_of_lt bot_le h')
    by_cases hk' : k = 0
    · simpa only [hk', JHFil]
    · conv_rhs =>
        arg 2; arg 2; arg 2
        rw [← Nat.sub_one_add_one hk']
      have hne : {p | ∃ (h : ⊥ < p), p < JHFil μ (k - 1) ∧ μ ⟨⊥, p, h⟩ =
          μ ⊤}.Nonempty := by
        by_contra!
        have this' : JHFil μ k = JHFil μ ((k - 1) + 1) :=
          congrArg (JHFil μ) (Nat.sub_one_add_one hk').symm
        simp only [this', JHFil, this] at hk
        simp only [Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt, lt_self_iff_false] at hk
      rw [← (hacc.wf.has_min _ hne).choose_spec.1.out.2.2] at this
      simp only [JHFil, hne]
      simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, gt_iff_lt, and_imp,
        forall_exists_index]
      simpa only [exists_and_left, Set.mem_ofPred_eq,
        gt_iff_lt, and_imp, forall_exists_index] using this
  · have h''' : μ ⟨⊥, z, lt_of_le_of_lt bot_le h'⟩ < μ ⊤ := by
      refine lt_of_le_of_ne this_q ?_
      by_contra!
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ k ∧
          μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
      · have := (hacc.wf.has_min _ hne).choose_spec.2 z (by use lt_of_le_of_lt bot_le h')
        simp only [JHFil, hne] at h'
        simp only [gt_iff_lt, exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this h'
      · exact hne ⟨z, lt_of_le_of_lt bot_le h', h'', this⟩
    have h'''' : μ ⊤ = μ ⟨⊥, JHFil μ (k + 1),
        bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ =
          μ ⊤}.Nonempty
      · simp only [JHFil, hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp only [gt_iff_lt, exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this.symm
      · simp only [JHFil, hne] at hfp1bot
        simp only [↓reduceDIte, not_true_eq_false] at hfp1bot
    exact (JHFil_step_payoff_eq_tot μ k hk).symm ▸ lt_trans ((Or.resolve_right <|
      (Or.resolve_left <| hsl.seesaw (bot_lt_iff_ne_bot.2 hfp1bot) h')
      (not_and_iff_not_or_not.2 <| Or.inl <| not_lt_of_gt <|
      h'''' ▸ h''')) (not_and_iff_not_or_not.2 <| Or.inl <| ne_of_gt <| h'''' ▸ h''')).2 h'''

/-- Existence of a Jordan–Hölder filtration: the greedy construction `JHFil` packages into
a `JordanHolderFiltration`.  In contrast to the Harder–Narasimhan filtration, a
Jordan–Hölder filtration is not unique, so existence is exposed as a `Nonempty` instance
rather than a canonical construction. -/
instance : Nonempty (μ.JordanHolderFiltration) :=
  ⟨{ toFun := JHFil μ
     length := JHlen μ
     antitone := JHFil_antitone μ
     head_eq_top := rfl
     length_eq_bot := JHFil_length_eq_bot μ
     strictAntiOn := JHFil_strictAntiOn μ
     step_payoff_eq := fun k hk ↦ JHFil_step_payoff_eq_tot μ k (JHFil_bot_lt μ hk)
     payoff_lt_of_between := fun i hi z h' h'' ↦
       JHFil_refine_lt_step_payoff μ i (JHFil_bot_lt μ hi) z h' h'' }⟩

/-- The `RelSeries` repackaging of the existence theorem: there is a finite chain for the
relation `μ.jordanHolderRel` whose head is `⊤` and whose last element is `⊥`. -/
theorem exists_relSeries_jordanHolderRel :
    ∃ s : RelSeries (μ.jordanHolderRel), s.head = ⊤ ∧ s.last = ⊥ := by
  obtain ⟨F⟩ := (inferInstance : Nonempty (μ.JordanHolderFiltration))
  exact ⟨{ length := F.length
           toFun := fun n ↦ F (n : ℕ)
           step := fun n ↦ ⟨F.apply_lt_apply (Nat.lt_add_one (n : ℕ)) (Fin.is_le n.succ),
             F.step_payoff n.isLt, fun z h' h'' ↦ F.payoff_lt n.isLt h' h''⟩ },
    F.apply_zero, F.apply_length⟩

end PayoffFunction

end HarderNarasimhan
