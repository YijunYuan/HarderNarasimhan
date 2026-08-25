/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Defs

/-!
# Existence of Harder–Narasimhan filtrations

This file constructs the canonical Harder–Narasimhan filtration `μ.hnFiltration` of a payoff
function `μ` on a well-founded bounded lattice, under the standing hypotheses `μ.ADCC`
(descending chain condition for `μ.A`), `μ.IsConvex`, and `μ.Admissible`.

The construction iterates the greatest-breakpoint step of
`HarderNarasimhan.PayoffFunction.Semistable.Breakpoints`: starting from `⊥`, as long as the
current term `x` is not `⊤`, the next term is the greatest breakpoint of `μ` on the interval
`(x, ⊤)`.  Well-foundedness of `>` on `ℒ` forces the chain to reach `⊤` after finitely many
steps, and the breakpoint properties provide semistability of the successive steps and the
strict decrease of the `μ.A`-slopes.  This is the existence half of the
existence-and-uniqueness theorem for Harder–Narasimhan filtrations; the uniqueness half is
proved in `HarderNarasimhan.Filtration.Unique`.

## Main definitions

* `PayoffFunction.hnFiltration` : the canonical Harder–Narasimhan filtration of `μ`, also
  available as `default` via the `Inhabited` instance.

## Main results

* `PayoffFunction.hnFiltration_succ_isGreatest_breakpoints` : the defining property of the
  canonical filtration; each successive term is the greatest breakpoint of the remaining top
  interval.
* `PayoffFunction.hnFiltration_A_bot_eq_A` : cutting a bottom-anchored interval at a term of
  the canonical filtration does not change the first-player value.
* `Inhabited (μ.HarderNarasimhanFiltration)` : Harder–Narasimhan filtrations exist.

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
/-- The canonical chain: starting from `⊥`, keep cutting at the greatest breakpoint of the
remaining top interval; once the chain reaches `⊤` it stays there. -/
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

/-- Specification of the defining choice in `HNFil`: before termination, the next term is a
greatest breakpoint of the remaining top interval. -/
private lemma HNFil_isGreatest (n : ℕ) (h' : HNFil μ n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨HNFil μ n, ⊤, h'.lt_top⟩) (HNFil μ (n + 1)) := by
  simp only [HNFil, h']
  exact (exists_isGreatest_breakpoints (I := ⟨HNFil μ n, ⊤, h'.lt_top⟩)
    ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
    (hadm.total_or_attained.imp id fun h z hzI hz ↦
      h ⟨HNFil μ n, z, lt_of_le_of_ne hzI.left hz⟩)).choose_spec

/-- One-step strict growth of `HNFil` before termination. -/
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
  have key : ∀ i j : ℕ, i < j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := fun i ↦
    Nat.le_induction
      (fun hi ↦ HNFil_lt_succ μ i ((HNFil_ne_top_iff μ i).2 hi))
      fun k _ hk' hk'' ↦
        lt_trans (hk' (le_trans (Nat.le_succ k) hk''))
          (HNFil_lt_succ μ k ((HNFil_ne_top_iff μ k).2 hk''))
  exact fun i _ j hj hij ↦ key i j hij hj

private lemma HNFil_length_eq_top : HNFil μ (HNlen μ) = ⊤ := by
  by_contra hc
  exact absurd le_rfl (not_le.2 ((HNFil_ne_top_iff μ (HNlen μ)).1 hc))

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

/-- Each successive step of `HNFil` is semistable, by the breakpoint property. -/
private lemma HNFil_piecewise_isSemistable :
    ∀ i : ℕ, (hi : i < HNlen μ) →
      (μ.restrict ⟨HNFil μ i, HNFil μ (i + 1),
        HNFil_strictMonoOn μ hi.le hi (lt_add_one i)⟩).IsSemistable :=
  fun i hi ↦ (mem_breakpoints.1
    (HNFil_isGreatest μ i ((HNFil_ne_top_iff μ i).2 hi)).1).isSemistable_restrict

/-- Strict decrease of the `μ.A`-slopes of successive steps of `HNFil`, from the obstruction
property of breakpoints. -/
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

/-- The **canonical Harder–Narasimhan filtration** of `μ`: starting from `⊥`, each successive
term is the greatest breakpoint of `μ` on the remaining top interval
(`hnFiltration_succ_isGreatest_breakpoints`), until the chain reaches `⊤`.

The hypotheses are the standing ones of the Harder–Narasimhan Games: the descending chain
condition `μ.ADCC` and well-foundedness of `>` on `ℒ` make the construction terminate,
convexity powers the breakpoint machinery, and `μ.Admissible` makes greatest breakpoints
exist.  Over a complete linear order this filtration is the unique one; see
`HarderNarasimhan.Filtration.Unique`.

The definition is not exposed: its body is built from the module-private recursion `HNFil`,
and downstream files interact with it through `hnFiltration_succ_isGreatest_breakpoints`. -/
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

/-- The defining property of the canonical filtration `μ.hnFiltration`: as long as the chain
has not reached `⊤`, the next term is the *greatest breakpoint* of `μ` on the remaining top
interval.  This is the main input to the uniqueness theorem of
`HarderNarasimhan.Filtration.Unique`. -/
lemma hnFiltration_succ_isGreatest_breakpoints {n : ℕ} (h : μ.hnFiltration n ≠ ⊤) :
    IsGreatest (μ.breakpoints ⟨μ.hnFiltration n, ⊤, h.lt_top⟩) (μ.hnFiltration (n + 1)) :=
  HNFil_isGreatest μ n h

/-- Cutting a bottom-anchored interval at a term of the canonical filtration does not change
the first-player value: for any `y` above the `n`-th term, the values `μ.A ⟨⊥, y⟩` and
`μ.A ⟨μ.hnFiltration n, y⟩` agree.  Since the terms below `μ.hnFiltration n` also lie below
`y`, instantiating at each index up to `n` packages the chain of equalities
`μ.A ⟨⊥, y⟩ = μ.A ⟨μ.hnFiltration 1, y⟩ = ⋯ = μ.A ⟨μ.hnFiltration n, y⟩`. -/
theorem hnFiltration_A_bot_eq_A {n : ℕ} {y : ℒ} (hy : μ.hnFiltration n < y) :
    μ.A ⟨⊥, y, bot_le.trans_lt hy⟩ = μ.A ⟨μ.hnFiltration n, y, hy⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmono : μ.hnFiltration n < y :=
      lt_of_le_of_lt ((μ.hnFiltration).monotone (Nat.le_succ n)) hy
    have hne : μ.hnFiltration n ≠ ⊤ := fun hc ↦ absurd (hc ▸ hmono) not_top_lt
    have hIB := mem_breakpoints.1 (hnFiltration_succ_isGreatest_breakpoints (μ := μ) hne).1
    have hstep := hIB.A_eq_A_of_lt ((inferInstance : μ.IsConvexOn ⊤).mono le_top)
      (hadm.total_or_attained.imp id fun h z hzI hz ↦
        h ⟨μ.hnFiltration n, z, lt_of_le_of_ne hzI.left hz⟩)
      ⟨hmono.le, le_top⟩ hy
    exact (ih hmono).trans hstep

end PayoffFunction

end HarderNarasimhan
