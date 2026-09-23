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

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
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
  simpa only [h', inf_top_eq] using hμcvx.inf_le_A haI hxI hzI hax h

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
  have hprev := breakpointAux_helper μ I i hi
  have hne : (improvingSet μ I (breakpointAux μ I i) hprev).Nonempty := by
    by_contra hempty
    simp only [breakpointAux, hprev, hempty, ↓reduceDIte, ne_eq, not_true_eq_false] at hi
  obtain ⟨hminI, hmin_bounds, hmin_improves⟩ :=
    hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) hprev) hne
  simp only [breakpointAux, hprev, hne, ↓reduceDIte] at hz ⊢
  intro hdominates
  -- A point above the chosen minimum with at least its value would also be a candidate.
  apply hwf.wf.not_lt_min (improvingSet μ I (breakpointAux μ I i) hprev) ?_ hz.1
  have hz_left : I.left < z := hminI.1.trans_lt hz.1
  refine ⟨⟨hz_left.le, hz.2.trans (breakpointAux μ I i).prop.2⟩,
    ⟨hz_left.ne, ?_⟩, hmin_improves.trans_le hdominates⟩
  apply lt_of_le_of_ne hz.2
  intro heq
  subst z
  exact hmin_improves.not_ge hdominates

private lemma breakpointAux_strict_decreasing (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) :
    ∀ i : ℕ, I.left ≠ (breakpointAux μ I i).val →
      (breakpointAux μ I i).val > (breakpointAux μ I (i+1)).val := by
  intro i hi
  by_cases hne : (improvingSet μ I (breakpointAux μ I i) hi).Nonempty
  · simpa only [breakpointAux, hi, hne, ↓reduceDIte] using
      (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I i) hi) hne).out.choose_spec.choose.2
  · simpa only [breakpointAux, hi, hne, ↓reduceDIte] using
      lt_of_le_of_ne (breakpointAux μ I i).prop.1 hi

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
  exact lt_of_le_of_ne (breakpointAux μ I i).prop.1
    (fun heq ↦ Nat.find_min (breakpointAux_fin_len μ I hμDCC) hi heq.symm)

private lemma breakpointAux_defprop3 (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)
    (hμDCC : μ.ADCC)
    (y : ℒ) (hy : I.left < y ∧ y ≤ (breakpointAux μ I <| (breakpointAux_len μ I hμDCC) - 1).val) :
    ¬ μ.A ⟨I.left, y, hy.1⟩ >
      μ.A ⟨I.left, (breakpointAux μ I <| (breakpointAux_len μ I hμDCC) - 1).val,
        breakpointAux_defprop3₀ μ I hμDCC ((breakpointAux_len μ I hμDCC) - 1) <| Nat.sub_one_lt <|
        breakpointAux_len_nonzero μ I hμDCC⟩ := by
  classical
  let len := breakpointAux_len μ I hμDCC
  have hlast : I.left < (breakpointAux μ I (len - 1)).val :=
    breakpointAux_defprop3₀ μ I hμDCC (len - 1)
      (Nat.sub_one_lt (breakpointAux_len_nonzero μ I hμDCC))
  intro himproves
  rcases hy.2.eq_or_lt with heq | hy_lt
  · simp only [heq, lt_self_iff_false] at himproves
  · -- A strict improvement would force another nonterminal step of the recursion.
    have hne : (improvingSet μ I (breakpointAux μ I (len - 1)) hlast.ne).Nonempty :=
      ⟨y, ⟨hy.1.le, hy.2.trans (breakpointAux μ I (len - 1)).prop.2⟩,
        ⟨hy.1.ne, hy_lt⟩, himproves⟩
    have hfinished : (breakpointAux μ I len).val = I.left :=
      Nat.find_spec (breakpointAux_fin_len μ I hμDCC)
    have hlen : len - 1 + 1 = len :=
      Nat.sub_one_add_one (breakpointAux_len_nonzero μ I hμDCC)
    rw [← hlen] at hfinished
    simp only [breakpointAux, hlast.ne, hne, ↓reduceDIte] at hfinished
    exact (hwf.wf.min_mem (improvingSet μ I (breakpointAux μ I (len - 1)) hlast.ne)
      hne).out.choose_spec.choose.1 hfinished.symm

/-- The set of breakpoints is nonempty: under the descending chain condition and convexity
on `I`, the breakpoint recursion terminates at a breakpoint.  This is the key existential
input to the Harder–Narasimhan filtration. -/
lemma breakpoints_nonempty [hμDCC : μ.ADCC] (hμcvx : μ.IsConvexOn I) :
    (μ.breakpoints I).Nonempty := by
  classical
  let len := breakpointAux_len μ I hμDCC
  let func := breakpointAux μ I
  have active : ∀ i : ℕ, i ≤ len - 1 → I.left < (func i).val := by
    intro i hi
    exact breakpointAux_defprop3₀ μ I hμDCC i
      (hi.trans_lt (Nat.sub_one_lt (breakpointAux_len_nonzero μ I hμDCC)))
  -- Convexity upgrades maximality inside a step to domination of all competing points.
  have step_dominates : ∀ i : ℕ, (hi : i + 1 ≤ len - 1) →
      ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) → y < func i →
      μ.A ⟨I.left, func (i + 1), active (i + 1) hi⟩ ≤
        μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ → y ≤ func (i + 1) := by
    intro i hi y hyI hy hy_prev hvalue
    by_contra hnot_le
    have hsup : (func (i + 1)).val < y ⊔ (func (i + 1)).val ∧
        y ⊔ (func (i + 1)).val ≤ (func i).val :=
      ⟨right_lt_sup.2 hnot_le, sup_le hy_prev.le
        (breakpointAux_strict_decreasing μ I i (active i (Nat.le_of_succ_le hi)).ne).le⟩
    apply breakpointAux_defprop2 μ I i (active (i + 1) hi).ne
      (y ⊔ (func (i + 1)).val) hsup
    simpa only [inf_eq_right.2 hvalue] using
      hμcvx.inf_A_le_A_sup hyI (func (i + 1)).prop I.left_mem
        (lt_of_le_of_ne hyI.1 hy) (active (i + 1) hi)
  -- Values increase along the recursion, so the last active value dominates all earlier ones.
  have value_le_final : ∀ i : ℕ, (hi : i ≤ len - 1) →
      μ.A ⟨I.left, func i, active i hi⟩ ≤
        μ.A ⟨I.left, func (len - 1), active (len - 1) le_rfl⟩ := by
    apply Nat.decreasingInduction
    · intro i hi ih
      exact (breakpointAux_defprop1 μ I i (active (i + 1) hi).ne).le.trans ih
    · exact le_rfl
  have final_dominates : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
      μ.A ⟨I.left, func (len - 1), active (len - 1) le_rfl⟩ ≤
        μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ →
      ∀ i : ℕ, i ≤ len - 1 → y ≤ (func i).val := by
    intro y hyI hy hvalue i hi
    induction i with
    | zero => exact hyI.2
    | succ i ih =>
      apply step_dominates i hi y hyI hy ?_ ((value_le_final (i + 1) hi).trans hvalue)
      refine lt_of_le_of_ne (ih (Nat.le_of_succ_le hi)) ?_
      intro heq
      have hstrict : μ.A ⟨I.left, func i, active i (Nat.le_of_succ_le hi)⟩ <
          μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ := calc
        _ < μ.A ⟨I.left, func (i + 1), active (i + 1) hi⟩ :=
          breakpointAux_defprop1 μ I i (active (i + 1) hi).ne
        _ ≤ μ.A ⟨I.left, func (len - 1), active (len - 1) le_rfl⟩ := value_le_final (i + 1) hi
        _ ≤ _ := hvalue
      simp only [heq, lt_self_iff_false] at hstrict
  refine ⟨(func (len - 1)).val, (func (len - 1)).prop, (active (len - 1) le_rfl).ne, ?_, ?_⟩
  · intro y hyI hy hbetter
    exact breakpointAux_defprop3 μ I hμDCC y
      ⟨lt_of_le_of_ne hyI.1 hy, final_dominates y hyI hy hbetter.le (len - 1) le_rfl⟩ hbetter
  · intro y hyI hy heq
    exact final_dominates y hyI hy heq.ge (len - 1) le_rfl

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
    ¬ μ.A ⟨I.left, x, hx.left_lt⟩ ≤ μ.A ⟨x, y, hy⟩ := by
  intro hslope
  have hy_left : I.left < y := hx.left_lt.trans hy
  apply hy.not_ge
  apply hx.le_of_eq y hyI hy_left.ne
  refine eq_of_le_of_not_lt' ?_ (hx.not_lt y hyI hy_left.ne)
  simpa only [inf_eq_left.2 hslope] using
    hμcvx.inf_le_A I.left_mem hx.mem hyI hx.left_lt hy

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
  rcases hμcvx.A_le_A_sup_or hx.mem hx'.mem I.left_mem hxlt hx'lt h₁ with hle | hle
  · have heq := eq_of_le_of_not_lt hle (hx.not_lt (x ⊔ x') hsI hsne)
    exact Or.inr (le_sup_right.trans (hx.le_of_eq (x ⊔ x') hsI hsne heq.symm))
  · have heq := eq_of_le_of_not_lt hle (hx'.not_lt (x ⊔ x') hsI hsne)
    exact Or.inl (le_sup_left.trans (hx'.le_of_eq (x ⊔ x') hsI hsne heq.symm))

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
