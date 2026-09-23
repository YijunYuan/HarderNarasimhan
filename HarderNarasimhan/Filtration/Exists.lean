/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Defs

/-!
# Existence of Harder–Narasimhan filtrations

A convex admissible payoff function with values in a complete lattice has a
Harder–Narasimhan filtration if it satisfies the descending chain condition on `μ.A` and
`>` is well-founded on the underlying nontrivial bounded lattice.

Starting from `⊥`, the construction takes the greatest breakpoint of the interval with
endpoints `x` and `⊤` as the successor of each term `x ≠ ⊤`. Well-foundedness of `>` ensures
that this increasing chain reaches `⊤` in finitely many steps. The breakpoint properties
give semistability of each step and `¬ aᵢ ≤ aᵢ₊₁` for successive `μ.A`-values.

## Main definitions

* `HarderNarasimhan.PayoffFunction.hnFiltration`: the filtration obtained by taking greatest
  breakpoints. It also supplies an `Inhabited` instance.

## Main results

* `HarderNarasimhan.PayoffFunction.hnFiltration_succ_isGreatest_breakpoints`: each term
  following a term below `⊤` is the greatest breakpoint of the remaining interval.
* `HarderNarasimhan.PayoffFunction.hnFiltration_A_bot_eq_A`: replacing the left endpoint `⊥`
  by a filtration term below the right endpoint preserves `μ.A`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hwf : WellFoundedGT ℒ]
variable {S : Type*} [CompleteLattice S]
variable (μ : PayoffFunction ℒ S) [μ.ADCC] [μ.IsConvex] [hadm : μ.Admissible]

open Classical in
/-- The chain starting at `⊥` whose successor terms are greatest breakpoints of the remaining
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

/-- Each term following a term below `⊤` is the greatest breakpoint of the remaining interval. -/
private lemma HNFil_isGreatest (n : ℕ) (h' : HNFil μ n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨HNFil μ n, ⊤, h'.lt_top⟩) (HNFil μ (n + 1)) := by
  simp only [HNFil, h']
  exact (exists_isGreatest_breakpoints (I := ⟨HNFil μ n, ⊤, h'.lt_top⟩)
    ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
    (hadm.total_or_attained.imp id fun h z hzI hz ↦
      h ⟨HNFil μ n, z, lt_of_le_of_ne hzI.left hz⟩)).choose_spec

/-- Each term below `⊤` is strictly less than its successor. -/
private lemma HNFil_lt_succ (n : ℕ) (hn : HNFil μ n ≠ ⊤) : HNFil μ n < HNFil μ (n + 1) :=
  lt_of_le_of_ne (HNFil_isGreatest μ n hn).1.1.1 (HNFil_isGreatest μ n hn).1.2

/-- `HNFil` reaches `⊤` in finite time, by well-foundedness of `>`. -/
private lemma HNFil_exists_eq_top : ∃ N : ℕ, HNFil μ N = ⊤ := by
  by_contra!
  exact (wellFounded_iff_isEmpty_descending_chain.1 hwf.wf).elim
    ⟨fun n ↦ HNFil μ n, fun n ↦ HNFil_lt_succ μ n (this n)⟩

open Classical in
/-- The least index at which `HNFil` reaches `⊤`. -/
private noncomputable def HNlen : ℕ := Nat.find (HNFil_exists_eq_top μ)

open Classical in
private lemma HNFil_ne_top_iff (n : ℕ) : HNFil μ n ≠ ⊤ ↔ n < HNlen μ := by
  refine ⟨fun hn ↦ ?_, Nat.find_min (HNFil_exists_eq_top μ)⟩
  by_contra!
  exact hn (Nat.le_induction (Nat.find_spec (HNFil_exists_eq_top μ))
    (fun k _ hk' ↦ by simp only [HNFil, hk', ↓reduceDIte]) n this)

private lemma HNFil_strictMonoOn : StrictMonoOn (HNFil μ) (Set.Iic (HNlen μ)) := by
  intro i _ j hj hij
  revert hj
  induction j, hij using Nat.le_induction with
  | base =>
    intro hj
    exact HNFil_lt_succ μ i ((HNFil_ne_top_iff μ i).2 hj)
  | succ j hij ih =>
    intro hj
    exact (ih (Nat.le_of_succ_le hj)).trans
      (HNFil_lt_succ μ j ((HNFil_ne_top_iff μ j).2 hj))

private lemma HNFil_length_eq_top : HNFil μ (HNlen μ) = ⊤ := by
  classical
  exact Nat.find_spec (HNFil_exists_eq_top μ)

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

/-- Each step of the chain before it reaches `⊤` is semistable. -/
private lemma HNFil_piecewise_isSemistable :
    ∀ i : ℕ, (hi : i < HNlen μ) →
      (μ.restrict ⟨HNFil μ i, HNFil μ (i + 1),
        HNFil_strictMonoOn μ hi.le hi (lt_add_one i)⟩).IsSemistable :=
  fun i hi ↦ (mem_breakpoints.1
    (HNFil_isGreatest μ i ((HNFil_ne_top_iff μ i).2 hi)).1).isSemistable_restrict

/-- No `μ.A`-value of a step is less than or equal to that of the next step. -/
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
  exact (mem_breakpoints.1 (HNFil_isGreatest μ i hi).1).not_A_le
    ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
    ⟨(lt_trans (HNFil_lt_succ μ i hi) hi').le, le_top⟩ hi'

/-- The Harder–Narasimhan filtration obtained by starting at `⊥` and successively taking the
greatest breakpoint of the remaining interval.

Use `HarderNarasimhan.PayoffFunction.hnFiltration_succ_isGreatest_breakpoints` for the
successor terms. For a complete linearly ordered codomain, this is the unique
Harder–Narasimhan filtration; see `HarderNarasimhan/Filtration/Unique.lean`. -/
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

/-- The canonical filtration provides a default Harder–Narasimhan filtration. -/
noncomputable instance : Inhabited (μ.HarderNarasimhanFiltration) := ⟨μ.hnFiltration⟩

variable {μ}

/-- Each term of the canonical filtration following a term below `⊤` is the greatest
breakpoint of the interval between that term and `⊤`. -/
lemma hnFiltration_succ_isGreatest_breakpoints {n : ℕ} (h : μ.hnFiltration n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨μ.hnFiltration n, ⊤, h.lt_top⟩) (μ.hnFiltration (n + 1)) :=
  HNFil_isGreatest μ n h

/-- Replacing the left endpoint `⊥` by a term of the canonical filtration preserves `μ.A`,
provided that the right endpoint lies strictly above that term. -/
theorem hnFiltration_A_bot_eq_A {n : ℕ} {y : ℒ} (hy : μ.hnFiltration n < y) :
    μ.A ⟨⊥, y, bot_le.trans_lt hy⟩ = μ.A ⟨μ.hnFiltration n, y, hy⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev_lt : μ.hnFiltration n < y :=
      lt_of_le_of_lt ((μ.hnFiltration).monotone (Nat.le_succ n)) hy
    have hne : μ.hnFiltration n ≠ ⊤ := (hprev_lt.trans_le le_top).ne
    have hbreakpoint := mem_breakpoints.1
      (hnFiltration_succ_isGreatest_breakpoints (μ := μ) hne).1
    calc
      _ = μ.A ⟨μ.hnFiltration n, y, hprev_lt⟩ := ih hprev_lt
      _ = _ := hbreakpoint.A_eq_A_of_lt ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
        (hadm.total_or_attained.imp id fun h z hzI hz ↦
          h ⟨μ.hnFiltration n, z, lt_of_le_of_ne hzI.left hz⟩)
        ⟨hprev_lt.le, le_top⟩ hy

end PayoffFunction

end HarderNarasimhan
