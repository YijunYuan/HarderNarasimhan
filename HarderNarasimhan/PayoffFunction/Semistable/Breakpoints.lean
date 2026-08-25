/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Convex
public import HarderNarasimhan.PayoffFunction.Semistable.Defs
public import Mathlib.Tactic.Linarith

/-!
# Existence and properties of breakpoints

This file proves the main structural facts about the breakpoints of a convex payoff function
on a well-founded lattice:

* existence (`breakpoints_nonempty`), by a well-founded recursion that repeatedly improves
  the candidate breakpoint;
* uniqueness over a linearly ordered codomain (`IsBreakpoint.eq`);
* semistability of the initial segment cut at a breakpoint
  (`IsBreakpoint.isSemistable_restrict`) and the obstruction above a breakpoint
  (`IsBreakpoint.not_A_le`);
* totality of the breakpoint set and existence of a greatest breakpoint
  (`breakpoints_total`, `exists_isGreatest_breakpoints`), and the decomposition formula
  `IsBreakpoint.A_eq_A_of_lt`, under a comparability or attainment hypothesis.

## Main results

* `breakpoints_nonempty` : existence of breakpoints.
* `IsBreakpoint.eq` : uniqueness over a complete linear order.
* `IsBreakpoint.isSemistable_restrict`, `IsBreakpoint.not_A_le` : semistability of the
  initial segment cut at a breakpoint, and the obstruction above a breakpoint.
* `breakpoints_total`, `exists_isGreatest_breakpoints`, `IsBreakpoint.A_eq_A_of_lt` :
  totality of the breakpoint set, existence of a greatest breakpoint, and the decomposition
  of the first-player value at a breakpoint.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [CompleteLattice S]
variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- If the first-player value on `(x, z)` is `⊤`, then enlarging an interval `(a, x)` to
`(a, z)` cannot decrease the first-player value.  This is the key step in deriving the
descending chain condition in `adcc_of_exists_A_eq_top`. -/
lemma IsConvexOn.A_le_of_A_eq_top (hμcvx : μ.IsConvexOn I) {x z : ℒ}
    (hxI : x ∈ I) (hzI : z ∈ I) (h : x < z) (h' : μ.A ⟨x, z, h⟩ = ⊤)
    {a : ℒ} (haI : a ∈ I) (hax : a < x) :
    μ.A ⟨a, x, hax⟩ ≤ μ.A ⟨a, z, lt_trans hax h⟩ := by
  have h'' := hμcvx.inf_le_A haI hxI hzI hax h
  rwa [h', inf_top_eq] at h''

/-- A convenient sufficient condition for `ADCC`: if every strictly descending chain
eventually produces a step with first-player value `⊤`, then the descending chain condition
holds. -/
lemma adcc_of_exists_A_eq_top [Nontrivial ℒ] [BoundedOrder ℒ] (hμcvx : μ.IsConvexOn ⊤)
    (h : ∀ f : ℕ → ℒ, (h : StrictAnti f) → ∃ N : ℕ, μ.A ⟨f <| N + 1, f N, h (lt_add_one N)⟩ = ⊤) :
    μ.ADCC := by
  refine { dcc := fun a f h₁ h₂ ↦ ?_ }
  obtain ⟨N, hN⟩ := h f h₂
  exact ⟨N, not_lt_of_ge <| hμcvx.A_le_of_A_eq_top (StrictIntvl.mem_top <| f <| N + 1)
    (StrictIntvl.mem_top <| f N) (h₂ (lt_add_one N)) hN (StrictIntvl.mem_top a) (h₁ <| N + 1)⟩

/-! ### The breakpoint recursion

The existence proof iterates the following step, starting from the right endpoint of `I`:
if some point strictly below the current candidate gives a strictly larger first-player
value, replace the candidate by a minimal such point (using well-foundedness of `>`).
The `ADCC` hypothesis forces this process to reach the left endpoint in finitely many
steps, and the last candidate before termination is a breakpoint. -/

section Recursion

variable [hwf : WellFoundedGT ℒ]

/-- The set of candidates strictly improving the current candidate `x`. -/
private def improvingSet (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (x : ↥I) (hx : I.left ≠ x) : Set ℒ :=
  {p : ℒ | ∃ h₁ : p ∈ I, ∃ h₂ : I.left ≠ p ∧ p < x,
    μ.A ⟨I.left, p, lt_of_le_of_ne h₁.1 h₂.1⟩ >
    μ.A ⟨I.left, x.val, lt_of_le_of_ne x.prop.1 hx⟩}

open Classical in
/-- The breakpoint recursion: start at the right endpoint and repeatedly move to a minimal
strictly improving point, stopping at the left endpoint. -/
private noncomputable def breakpointAux (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (k : ℕ) : ↥I :=
  match k with
  | 0 => ⟨I.right, I.right_mem⟩
  | n + 1 =>
    let prev := breakpointAux μ I n
    if hbot : I.left = prev.val then
      ⟨I.left, I.left_mem⟩
    else
      if hne : (improvingSet μ I prev hbot).Nonempty then
        ⟨hwf.wf.min (improvingSet μ I prev hbot) hne,
          (hwf.wf.min_mem (improvingSet μ I prev hbot) hne).out.choose⟩
      else
        ⟨I.left, I.left_mem⟩

private lemma breakpointAux_helper (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (i : ℕ) (hi : I.left ≠ (breakpointAux μ I (i + 1)).val) :
    I.left ≠ (breakpointAux μ I i).val := by
  by_contra hcontra
  simp only [breakpointAux, hcontra, ↓reduceDIte, ne_eq, not_true_eq_false] at hi

private lemma breakpointAux_defprop1 (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (i : ℕ) (hi : I.left ≠ (breakpointAux μ I (i + 1)).val) :
    μ.A ⟨I.left, (breakpointAux μ I (i+1)).val,
        lt_of_le_of_ne (breakpointAux μ I (i+1)).prop.1 hi⟩ >
      μ.A ⟨I.left, (breakpointAux μ I i).val,
        lt_of_le_of_ne ((breakpointAux μ I i)).prop.1 <| breakpointAux_helper μ I i hi⟩ := by
  have hne :
      (improvingSet μ I (breakpointAux μ I i) <| breakpointAux_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [breakpointAux, breakpointAux_helper μ I i hi, hcontra, ↓reduceDIte, ne_eq,
      not_true_eq_false] at hi
  simpa only [breakpointAux, breakpointAux_helper μ I i hi, hne, ↓reduceDIte] using
    (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) <|
      breakpointAux_helper μ I i hi) hne).out.choose_spec.choose_spec

private lemma breakpointAux_defprop2 (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (i : ℕ) (hi : I.left ≠ (breakpointAux μ I (i + 1)).val) :
    ∀ z : ℒ, (hz : (breakpointAux μ I (i+1)).val < z ∧ z ≤ (breakpointAux μ I i).val) →
      ¬ μ.A ⟨I.left, z, lt_of_le_of_lt (breakpointAux μ I (i+1)).prop.1 hz.1⟩ ≥
        μ.A ⟨I.left, (breakpointAux μ I (i+1)).val,
          lt_of_le_of_ne (breakpointAux μ I (i+1)).prop.1 hi⟩ := by
  intro z hz
  have hne :
      (improvingSet μ I (breakpointAux μ I i) <| breakpointAux_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [breakpointAux, breakpointAux_helper μ I i hi, hcontra, ↓reduceDIte, ne_eq,
      not_true_eq_false] at hi
  simp only [breakpointAux, breakpointAux_helper μ I i hi, hne]
  by_contra hcontra
  have h' : z ∈ (improvingSet μ I (breakpointAux μ I i) <| breakpointAux_helper μ I i hi) := by
    use ⟨le_of_lt <| lt_of_le_of_lt (breakpointAux μ I (i + 1)).prop.1 hz.1,
      le_trans hz.2 (breakpointAux μ I i).prop.2⟩
    have h'' : z < (breakpointAux μ I i).val := by
      apply lt_of_le_of_ne hz.2
      intro hcontra'
      simp only [hcontra', ↓reduceDIte, ge_iff_le] at hcontra
      exact (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) <|
        breakpointAux_helper μ I i hi) hne).out.choose_spec.choose_spec.not_ge hcontra
    use ⟨ne_of_lt <| lt_of_le_of_lt (breakpointAux μ I (i+1)).prop.1 hz.1, h''⟩, lt_of_le_of_lt'
      hcontra.ge (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) <|
        breakpointAux_helper μ I i hi) hne).out.choose_spec.choose_spec
  simp only [breakpointAux, breakpointAux_helper μ I i hi, hne] at hz
  exact hwf.wf.not_lt_min (improvingSet μ I (breakpointAux μ I i) <|
    breakpointAux_helper μ I i hi) h' hz.1

private lemma breakpointAux_strict_decreasing (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) :
    ∀ i : ℕ, I.left ≠ (breakpointAux μ I i).val →
      (breakpointAux μ I i).val > (breakpointAux μ I (i+1)).val := by
  intro i hi
  by_cases h : I.left = (breakpointAux μ I (i+1)).val
  · simp only [breakpointAux, hi, ↓reduceDIte] at h
    by_cases hne : (improvingSet μ I (breakpointAux μ I i) hi).Nonempty
    · simp only [hne, ↓reduceDIte] at h
      exact False.elim ((hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) hi) hne
        ).out.choose_spec.choose.1 h)
    · simp only [breakpointAux, hi, hne]
      exact lt_of_le_of_ne (breakpointAux μ I i).prop.1 hi
  · simp only [breakpointAux, hi, ↓reduceDIte]
    have hne :
        (improvingSet μ I (breakpointAux μ I i) <| breakpointAux_helper μ I i h).Nonempty := by
      by_contra hcontra
      simp only [breakpointAux, breakpointAux_helper μ I i h, hcontra,
        ↓reduceDIte, not_true_eq_false] at h
    simpa only [hne, ↓reduceDIte] using (hwf.wf.min_mem
      (improvingSet μ I (breakpointAux μ I i) hi) hne).out.choose_spec.choose.2

private lemma breakpointAux_fin_len (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC) :
    ∃ i : ℕ, (breakpointAux μ I i).val = I.left := by
  by_contra!
  obtain ⟨N, hN⟩ := hμDCC.dcc I.left (fun m ↦ (breakpointAux μ I m).val)
    (fun i ↦ Ne.lt_of_le (this i).symm (breakpointAux μ I i).prop.1)
    (strictAnti_nat_of_succ_lt fun t ↦ breakpointAux_strict_decreasing μ I t (this t).symm)
  exact hN (breakpointAux_defprop1 μ I N (this (N + 1)).symm)

open Classical in
private noncomputable def breakpointAux_len (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC) : ℕ :=
  Nat.find (breakpointAux_fin_len μ I hμDCC)

private lemma breakpointAux_len_nonzero (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC) :
    breakpointAux_len μ I hμDCC ≠ 0 := by
  classical
  by_contra hcontra
  have h : (breakpointAux μ I (breakpointAux_len μ I hμDCC)).val = I.left :=
    Nat.find_spec (breakpointAux_fin_len μ I hμDCC)
  simp only [hcontra, breakpointAux] at h
  exact (h ▸ I.lt).false

private lemma breakpointAux_defprop3₀ (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC)
    (i : ℕ) (hi : i < (breakpointAux_len μ I hμDCC)) :
    I.left < (breakpointAux μ I i).val := by
  classical
  exact ((Nat.find_min (breakpointAux_fin_len μ I hμDCC)) hi).decidable_imp_symm
    fun hcontra ↦ (eq_of_le_of_not_lt (breakpointAux μ I i).prop.1 hcontra).symm

private lemma breakpointAux_defprop3 (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC)
    (y : ℒ) (hy : I.left < y ∧ y ≤ (breakpointAux μ I <| (breakpointAux_len μ I hμDCC) - 1).val) :
    ¬ μ.A ⟨I.left, y, hy.1⟩ >
      μ.A ⟨I.left, (breakpointAux μ I <| (breakpointAux_len μ I hμDCC) - 1).val,
        breakpointAux_defprop3₀ μ I hμDCC ((breakpointAux_len μ I hμDCC) - 1) <| Nat.sub_one_lt <|
        breakpointAux_len_nonzero μ I hμDCC⟩ := by
  classical
  let len := breakpointAux_len μ I hμDCC
  by_contra hcontra
  by_cases hcases : y < (breakpointAux μ I (len - 1)).val
  · have h₂ : (breakpointAux μ I len).val = I.left :=
      Nat.find_spec (breakpointAux_fin_len μ I hμDCC)
    have h₃ : ¬ (improvingSet μ I (breakpointAux μ I <| len - 1)
        (ne_of_lt <| breakpointAux_defprop3₀ μ I hμDCC (len - 1)
          (Nat.sub_one_lt <| breakpointAux_len_nonzero μ I hμDCC))).Nonempty := by
      by_contra hcontra'
      have triv : len - 1 + 1 = len := Nat.sub_one_add_one <| breakpointAux_len_nonzero μ I hμDCC
      rw [← triv] at h₂
      simp only [breakpointAux, ne_of_lt <| breakpointAux_defprop3₀ μ I hμDCC (len - 1)
        (Nat.sub_one_lt <| breakpointAux_len_nonzero μ I hμDCC), hcontra', ↓reduceDIte] at h₂
      exact (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I (len-1)) (ne_of_lt <|
        breakpointAux_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <|
        breakpointAux_len_nonzero μ I hμDCC))) hcontra').out.choose_spec.choose.1
        h₂.symm
    exact h₃ ⟨y, ⟨le_of_lt hy.1, le_trans hy.2 (breakpointAux μ I (len - 1)).prop.2⟩,
      ⟨ne_of_lt hy.1, hcases⟩, hcontra⟩
  · simp only [eq_of_le_of_not_lt hy.2 hcases] at hcontra
    exact lt_irrefl _ hcontra

/-- The set of breakpoints is nonempty: under the descending chain condition and convexity
on `I`, the breakpoint recursion terminates at a breakpoint.  This is the key existential
input to the Harder–Narasimhan filtration. -/
lemma breakpoints_nonempty [hμDCC : μ.ADCC] (hμcvx : μ.IsConvexOn I) :
    (μ.breakpoints I).Nonempty := by
  classical
  let len := breakpointAux_len μ I hμDCC
  let func := breakpointAux μ I
  by_cases h : len = 1
  · refine ⟨I.right, I.right_mem, I.lt.ne, ?_, fun _ hyI _ _ ↦ hyI.2⟩
    intro y hyI hy
    have h' : (breakpointAux μ I (breakpointAux_len μ I hμDCC - 1)).val = I.right :=
      congrArg (fun a ↦ (func (a - 1)).val) h
    simpa only [h', Prod.mk.eta, Subtype.coe_eta, gt_iff_lt] using
      breakpointAux_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.left hy, h' ▸ hyI.2⟩
  · have h₂ : ∀ i : ℕ, i ≤ len - 1 → I.left ≠ (func i).val := by
      intro i hi
      by_contra!
      exact (Nat.find_min (breakpointAux_fin_len μ I hμDCC) <| Nat.lt_of_le_sub_one
        (Nat.zero_lt_of_ne_zero <| breakpointAux_len_nonzero μ I hμDCC) hi) this.symm
    have h₃ : ∀ i : ℕ, (hi : 1 ≤ i ∧ i ≤ len - 1) → (∀ y : ℒ, (hyI : y ∈ I) →
        (hy : I.left ≠ y) → (y < func (i-1) ∧ μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ ≥
        μ.A ⟨I.left, (func i).val, lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩) →
        y ≤ (func i).val) := by
      intro i hi y hyI hy hy'
      by_contra!
      have h₃' : (func i).val < y ⊔ (func i).val ∧ y ⊔ (func i).val ≤ (func (i-1)).val := by
        refine ⟨right_lt_sup.2 this, sup_le_iff.2 ⟨le_of_lt hy'.1, ?_⟩⟩
        have h₃'' := breakpointAux_strict_decreasing μ I (i-1) (h₂ (i-1) <| le_trans (le_of_lt <|
          Nat.sub_one_lt <| Nat.one_le_iff_ne_zero.1 hi.1) hi.2)
        rw [Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1] at h₃''
        exact le_of_lt h₃''
      have h₃''' : ∀ (hi' : I.left ≠ (func i).val) (z : ℒ) (hz : (func i).val < z ∧
          z ≤ (func (i - 1)).val), ¬ μ.A ⟨I.left, z, lt_of_le_of_lt (func i).prop.1 hz.1⟩ ≥
          μ.A ⟨I.left, (func (i - 1 + 1)).val, lt_of_le_of_ne ((func (i - 1 + 1)).prop).1
            ((Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2)⟩ :=
        fun hi' z hz ↦ breakpointAux_defprop2 μ I (i - 1) ((Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2) z ((Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ hz)
      simp only [ne_eq, not_false_eq_true, Nat.sub_add_cancel, ge_iff_le, forall_const, hi,
        h₂] at h₃'''
      exact (h₃''' (y ⊔ func i) h₃') <| inf_eq_right.2 hy'.2 ▸
        hμcvx.inf_A_le_A_sup hyI (func i).prop I.left_mem
          (lt_of_le_of_ne hyI.1 hy) (lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2)
    have h₄ : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) → μ.A ⟨I.left, y,
        lt_of_le_of_ne hyI.1 hy⟩ ≥ μ.A ⟨I.left, (func (len - 1)).val, lt_of_le_of_ne (func
        (len - 1)).prop.1 <| h₂ (len - 1) le_rfl⟩ → (∀ i : ℕ, i ≤ len - 1 → y ≤ (func i).val) := by
      intro y hyI hy hy' i hi
      induction i with
      | zero => exact hyI.2
      | succ i hi' =>
        have hfinal : ∀ j : ℕ, (hj : j ≤ len - 1) → μ.A ⟨I.left, (func (len - 1)).val,
            lt_of_le_of_ne ((func (len - 1)).prop).1 (h₂ (len - 1) le_rfl)⟩ ≥
            μ.A ⟨I.left, func j,
            breakpointAux_defprop3₀ μ I hμDCC j <| lt_of_le_of_lt hj <| Nat.sub_one_lt <|
            ne_of_gt <| Nat.zero_lt_of_ne_zero <| breakpointAux_len_nonzero μ I hμDCC⟩ := by
          apply Nat.decreasingInduction
          · exact fun k hk hk' ↦ le_of_lt <| lt_of_lt_of_le (breakpointAux_defprop1 μ I k <|
              ne_of_lt <| breakpointAux_defprop3₀ μ I hμDCC (k+1) <| Nat.add_lt_of_lt_sub hk) hk'
          · exact le_rfl
        have hh : y < func i := by
          refine lt_of_le_of_ne (hi' (Nat.le_of_succ_le hi)) ?_
          intro heq
          have hhh := lt_of_le_of_lt' hy' <| lt_of_le_of_lt' (hfinal (i+1) hi) <|
            breakpointAux_defprop1 μ I i (ne_of_lt <| breakpointAux_defprop3₀ μ I hμDCC (i+1) <|
            lt_of_le_of_lt hi <| Nat.sub_one_lt <| ne_of_gt <| Nat.zero_lt_of_ne_zero <|
            breakpointAux_len_nonzero μ I hμDCC)
          simp only [heq] at hhh
          exact irrefl _ hhh
        exact h₃ (i+1) ⟨Nat.le_add_left 1 i, hi⟩ y hyI hy ⟨hh, ge_trans hy' (hfinal (i+1) hi)⟩
    refine ⟨(func (len - 1)).val, (func (len - 1)).prop, h₂ (len - 1) le_rfl, ?_,
      fun y hyI hy hy' ↦ h₄ y hyI hy (ge_of_eq hy') (len - 1) le_rfl⟩
    intro y hyI hy
    by_contra!
    exact breakpointAux_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.1 hy,
      h₄ y hyI hy (le_of_lt this) (len - 1) le_rfl⟩ this

end Recursion

section LinearOrder

variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Over a complete linear order the breakpoint is unique. -/
lemma IsBreakpoint.eq {x y : ℒ} (hx : μ.IsBreakpoint I x) (hy : μ.IsBreakpoint I y) : x = y := by
  have e := eq_of_le_of_ge (le_of_not_gt <| hx.not_lt y hy.mem hy.ne_left)
    (le_of_not_gt <| hy.not_lt x hx.mem hx.ne_left)
  exact eq_of_le_of_ge (hy.le_of_eq x hx.mem hx.ne_left e.symm) (hx.le_of_eq y hy.mem hy.ne_left e)

end LinearOrder

/-- A breakpoint of `I` is a breakpoint of the initial segment it cuts. -/
lemma IsBreakpoint.isBreakpoint_left {x : ℒ} (hx : μ.IsBreakpoint I x) :
    μ.IsBreakpoint ⟨I.left, x, hx.left_lt⟩ x where
  mem := ⟨hx.mem.1, le_rfl⟩
  ne_left := hx.ne_left
  not_lt := fun z hzI hz ↦ hx.not_lt z ⟨hzI.1, le_trans hzI.2 hx.mem.2⟩ hz
  le_of_eq := fun z hzI hz hz' ↦ hx.le_of_eq z ⟨hzI.1, le_trans hzI.2 hx.mem.2⟩ hz hz'

/-- The initial segment cut at a breakpoint is semistable. -/
lemma IsBreakpoint.isSemistable_restrict {x : ℒ} (hx : μ.IsBreakpoint I x) :
    (μ.restrict ⟨I.left, x, hx.left_lt⟩).IsSemistable :=
  isBreakpoint_right_iff.1 hx.isBreakpoint_left

/-- Above a breakpoint the first-player value cannot be dominated: for `y > x` in `I` the
value on `(x, y)` does not dominate the value on `(I.left, x)`. -/
lemma IsBreakpoint.not_A_le {x : ℒ} (hx : μ.IsBreakpoint I x) (hμcvx : μ.IsConvexOn I)
    {y : ℒ} (hyI : y ∈ I) (hy : x < y) :
    ¬ μ.A ⟨I.left, x, hx.left_lt⟩ ≤ μ.A ⟨x, y, hy⟩ := fun hy' ↦
  (not_le_of_gt hy) (hx.le_of_eq y hyI (ne_of_lt <| lt_of_le_of_lt hx.mem.1 hy) <|
    eq_of_le_of_not_lt' ((inf_eq_left.2 hy') ▸
      hμcvx.inf_le_A I.left_mem hx.mem hyI hx.left_lt hy) <|
    hx.not_lt y hyI <| ne_of_lt <| lt_of_le_of_lt hx.mem.1 hy)

section Total

variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Under convexity and a comparability or attainment hypothesis, the breakpoints of `I`
are totally ordered. -/
lemma breakpoints_total (hμcvx : μ.IsConvexOn I)
    (h : (Std.Total (· ≤ · : S → S → Prop)) ∨
      ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
        μ.IsAttained ⟨I.left, z, lt_of_le_of_ne hzI.left hz⟩) :
    @Std.Total (μ.breakpoints I) (· ≤ ·) := by
  refine { total := ?_ }
  rintro ⟨x, hx⟩ ⟨x', hx'⟩
  replace hx := mem_breakpoints.1 hx
  replace hx' := mem_breakpoints.1 hx'
  have hxlt : I.left < x := hx.left_lt
  have hx'lt : I.left < x' := hx'.left_lt
  have hsI : (x ⊔ x') ∈ I := ⟨le_sup_of_le_left hx.mem.1, sup_le hx.mem.2 hx'.mem.2⟩
  have hsne : I.left ≠ x ⊔ x' := ne_of_lt <| lt_sup_of_lt_left hxlt
  have h₁ : Relation.SymmGen (· ≤ ·) (μ.A ⟨I.left, x, hxlt⟩) (μ.A ⟨I.left, x', hx'lt⟩) ∨
      μ.IsAttained ⟨I.left, x ⊔ x', lt_sup_of_lt_right hx'lt⟩ := by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total _ _
    · exact Or.inr <| hattained (x ⊔ x') hsI hsne
  have h₂ : μ.A ⟨I.left, x, hxlt⟩ = μ.A ⟨I.left, x ⊔ x', lt_sup_of_lt_left hxlt⟩ ∨
      μ.A ⟨I.left, x', hx'lt⟩ = μ.A ⟨I.left, x ⊔ x', lt_sup_of_lt_left hxlt⟩ := by
    rcases hμcvx.A_le_A_sup_or hx.mem hx'.mem I.left_mem hxlt hx'lt h₁ with c1 | c2
    · exact Or.inl <| eq_of_le_of_not_lt c1 <| hx.not_lt (x ⊔ x') hsI hsne
    · exact Or.inr <| eq_of_le_of_not_lt c2 <| hx'.not_lt (x ⊔ x') hsI hsne
  rcases h₂ with c1 | c2
  · exact Or.inr (sup_le_iff.1 <| hx.le_of_eq (x ⊔ x') hsI hsne c1.symm).2
  · exact Or.inl (sup_le_iff.1 <| hx'.le_of_eq (x ⊔ x') hsI hsne c2.symm).1

/-- Under the descending chain condition, convexity, and a comparability or attainment
hypothesis, the set of breakpoints has a greatest element.  This is the existence input for
the canonical Harder–Narasimhan filtration. -/
lemma exists_isGreatest_breakpoints [hwf : WellFoundedGT ℒ] [μ.ADCC] (hμcvx : μ.IsConvexOn I)
    (h : (Std.Total (· ≤ · : S → S → Prop)) ∨
      ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
        μ.IsAttained ⟨I.left, z, lt_of_le_of_ne hzI.left hz⟩) :
    ∃ s : ℒ, IsGreatest (μ.breakpoints I) s := by
  obtain ⟨M, hM⟩ := hwf.wf.has_min (μ.breakpoints I) (breakpoints_nonempty hμcvx)
  refine ⟨M, hM.1, mem_upperBounds.2 fun x hx ↦ ?_⟩
  exact ((breakpoints_total hμcvx h).total ⟨x, hx⟩ ⟨M, hM.1⟩).elim id
    fun c2 ↦ le_of_eq <| eq_of_le_of_not_lt' c2 (hM.2 x hx)

/-- Decomposition at a breakpoint: for `y` above a breakpoint `x`, the first-player value on
`(I.left, y)` is computed on `(x, y)`. -/
lemma IsBreakpoint.A_eq_A_of_lt {x : ℒ} (hx : μ.IsBreakpoint I x) (hμcvx : μ.IsConvexOn I)
    (h : (Std.Total (· ≤ · : S → S → Prop)) ∨
      ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
        μ.IsAttained ⟨I.left, z, lt_of_le_of_ne hzI.left hz⟩)
    {y : ℒ} (hyI : y ∈ I) (hxy : x < y) :
    μ.A ⟨I.left, y, lt_of_le_of_lt hx.mem.1 hxy⟩ = μ.A ⟨x, y, hxy⟩ := by
  have hyne : I.left ≠ y := ne_of_lt <| lt_of_le_of_lt hx.mem.1 hxy
  have h' : Relation.SymmGen (· ≤ ·) (μ.A ⟨I.left, x, hx.left_lt⟩) (μ.A ⟨x, y, hxy⟩) ∨
      μ.IsAttained ⟨I.left, y, lt_of_le_of_lt hx.mem.1 hxy⟩ := by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total _ _
    · exact Or.inr <| hattained y hyI hyne
  rcases hμcvx.A_eq_or_lt I.left_mem hx.mem hyI hx.left_lt hxy h' with c1 | c2
  · exact c1.symm
  · exact absurd hxy <| not_lt_of_ge <| hx.le_of_eq y hyI hyne <|
      eq_of_le_of_not_lt' c2.1 (hx.not_lt y hyI hyne)

end Total

end PayoffFunction

end HarderNarasimhan
