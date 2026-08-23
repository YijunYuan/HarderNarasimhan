/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Filtration.Defs

/-!
Implementation of the canonical Harder–Narasimhan filtration.

This file constructs, under the standard hypotheses (DCC for `μA`, convexity, and
admissibility), a canonical filtration `HNFil μ : ℕ → ℒ` by iterating the following
step:

* given the current term `x`, look at the interval `(x, ⊤)` and pick a greatest
  element of the stable set `StI μ (x, ⊤)`.

The main outcomes provided here are:

* finiteness of the process via well-foundedness (`HNFil_of_fin_len`, `HNlen`),
* strict monotonicity up to the stopping time (`HNFil_is_strict_mono'`),
* semistability of each successive restricted interval
  (`HNFil_piecewise_semistable`), and
* the strict decrease condition on successive `μA`-slopes
  (`HNFil_μA_pseudo_strict_anti`).

Finally, `theorem3d10` is a uniqueness statement: any filtration satisfying the
expected axioms coincides with the canonical one.

The last section provides utilities for translating between filtrations and
`RelSeries (IntervalSemistableRel μ)`.

API note: this file is intentionally kept under the internal namespace `HarderNarasimhan.impl`
and is not meant to be imported directly by downstream developments. For a stable interface,
import `HarderNarasimhan.Filtration.Results`.
-/

namespace HarderNarasimhan

namespace impl

open Classical in
/--
The canonical Harder–Narasimhan filtration sequence.

* Base case: `HNFil μ 0 = ⊥`.
* Step: if the previous term is already `⊤`, we stay at `⊤`; otherwise we choose a
  greatest element in the stable set on the interval `(prev_term, ⊤)`.

The definition is noncomputable because it uses choice (`Classical.choose`) to pick
greatest elements.
-/
noncomputable def HNFil {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ]
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNFil μ n
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨prev_term, ⊤ , lt_top_iff_ne_top.2 htop⟩ : Intvl ℒ)
      (impl.prop3d8₁' μ hμ I' (Convex_of_Convex_large TotIntvl I' ⟨bot_le,le_top⟩ μ hμcvx)
      (Or.casesOn h.μ_adm (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨I'.left, z ,  lt_of_le_of_ne hzI.left hz⟩)).choose


/-- Specification lemma for the defining choice in `HNFil`.

    If `HNFil μ n` is not yet `⊤`, then `HNFil μ (n+1)` is a greatest element of the
    stable set on the tail interval `(HNFil μ n, ⊤)`.

    This lemma is used to derive strict monotonicity and the semistability/slope
    properties of the successive steps.
-/
lemma HNFil_prop_of_def {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ n : Nat, (h' : HNFil μ n ≠ ⊤) →
IsGreatest (StI μ ⟨HNFil μ n, ⊤, lt_top_iff_ne_top.2 h'⟩) (HNFil μ (n + 1)) := by
  intro n h'
  simp only [HNFil, h']
  exact (impl.prop3d8₁' μ hμ ⟨HNFil μ n, ⊤, h'.lt_top⟩
    (Convex_of_Convex_large TotIntvl _ ⟨bot_le,le_top⟩ μ hμcvx)
    (Or.casesOn h.μ_adm (fun h ↦ Or.inl h) fun h ↦
     Or.inr fun z hzI hz ↦ h ⟨HNFil μ n, z, lt_of_le_of_ne hzI.left hz⟩)).choose_spec


/--
One-step strict growth of `HNFil` before termination.

As long as `HNFil μ n ≠ ⊤`, the next term is strictly larger. This is obtained from
the “greatest element” property in `HNFil_prop_of_def`.
-/
lemma HNFil_is_strict_mono {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ n : Nat, HNFil μ n ≠ ⊤ → HNFil μ n < HNFil μ (n + 1) := fun
    n hn ↦ lt_of_le_of_ne (HNFil_prop_of_def μ n hn).1.1.1 (HNFil_prop_of_def μ n hn).1.2.1


/--
`HNFil` reaches `⊤` in finite time.

If it never reached `⊤`, the strict monotonicity lemma would produce an infinite
descending chain in the `>` well-founded order, contradicting `WellFoundedGT ℒ`.
-/
lemma HNFil_of_fin_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[inst_3 : WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ]
: ∃ N : Nat, HNFil μ N = ⊤ := by
  by_contra!
  exact (wellFounded_iff_isEmpty_descending_chain.1 inst_3.wf).elim
    ⟨fun n => HNFil μ n, fun n => HNFil_is_strict_mono μ n (this n)⟩

open Classical in
/-- The length of the canonical filtration.

  Defined as the minimal `N` such that `HNFil μ N = ⊤`.
-/
noncomputable def HNlen {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] : Nat := Nat.find (HNFil_of_fin_len μ)

open Classical in
  /--
  Characterization of “not yet terminated” via `HNlen`.

  This is the expected property of `Nat.find`: `HNFil μ n ≠ ⊤` iff `n < HNlen μ`.
  -/
lemma HNFil_ne_top_iff_lt_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
  ∀ n : Nat, HNFil μ n ≠ ⊤ ↔ n < HNlen μ := by
  intro n
  refine ⟨fun hn ↦ ?_, Nat.find_min (HNFil_of_fin_len μ)⟩
  by_contra!
  exact hn (Nat.le_induction (Nat.find_spec (HNFil_of_fin_len μ))
    (fun k _ hk' ↦ by simp only [HNFil, hk', ↓reduceDIte]) n this)


/--
Strict monotonicity of `HNFil` on the active range.

If `i < j ≤ HNlen μ`, then `HNFil μ i < HNFil μ j`.
-/
lemma HNFil_is_strict_mono' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := fun i ↦
  Nat.le_induction
    (fun hi ↦ HNFil_is_strict_mono μ i ((HNFil_ne_top_iff_lt_len μ i).2 hi))
    fun k _ hk' hk'' ↦
      lt_trans (hk' (le_trans (Nat.le_succ k) hk''))
        (HNFil_is_strict_mono μ k ((HNFil_ne_top_iff_lt_len μ k).2 hk''))

open Classical in
/--
Each successive interval of `HNFil` is semistable.

This is exactly the `piecewise_semistable` axiom of a Harder–Narasimhan filtration,
proved using the semistability statement for stable breakpoints (`prop3d7₁`) and the
translation lemma `semistableI_iff`.
-/
lemma HNFil_piecewise_semistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ] [h : μ_Admissible μ] :
∀ i : ℕ, (h: i < Nat.find (HNFil_of_fin_len μ)) →
    Semistable (Resμ ⟨HNFil μ i, HNFil μ (i+1),
      HNFil_is_strict_mono' μ i (i+1) (lt_add_one i) h⟩ μ) :=
  fun i hi ↦ (semistableI_iff μ ⟨HNFil μ i, HNFil μ (i+1),
    HNFil_is_strict_mono' μ i (i+1) (lt_add_one i) hi⟩).1 <|
    impl.prop3d7₁ μ ⟨HNFil μ i, ⊤, lt_top_iff_ne_top.2 <|
    Nat.find_min (HNFil_of_fin_len μ) hi⟩ (HNFil μ (i + 1))
    (HNFil_prop_of_def μ i (Nat.find_min (HNFil_of_fin_len μ) hi)).1

open Classical in
/--
Strict decrease condition on consecutive `μA`-slopes for `HNFil`.

This is the analogue of “HN slopes are strictly decreasing”, phrased as the
non-comparability statement `¬ μA(i,i+1) ≤ μA(i+1,i+2)`.

The proof is an application of the internal obstruction lemma `prop3d7₂`.
-/
lemma HNFil_μA_pseudo_strict_anti {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ] [h : μ_Admissible μ] :
∀ i : ℕ, (hi : i + 1 < Nat.find (HNFil_of_fin_len μ)) →
  ¬ μA μ ⟨HNFil μ i, HNFil μ (i+1),
      HNFil_is_strict_mono μ i (Nat.find_min (HNFil_of_fin_len μ) (Nat.lt_of_succ_lt hi))⟩ ≤
    μA μ ⟨HNFil μ (i+1), HNFil μ (i+2),
      HNFil_is_strict_mono μ (i + 1) (Nat.find_min (HNFil_of_fin_len μ) hi)⟩ := by
  intro i hj
  have hi : HNFil μ i ≠ ⊤ := Nat.find_min (HNFil_of_fin_len μ) (lt_trans (lt_add_one i) hj)
  have hi' : HNFil μ (i + 1) < HNFil μ (i + 1 + 1) :=
    HNFil_is_strict_mono μ (i + 1) (Nat.find_min (HNFil_of_fin_len μ) hj)
  exact impl.prop3d7₂ μ ⟨HNFil μ i, ⊤, lt_top_iff_ne_top.2 hi⟩
    (Convex_of_Convex_large TotIntvl ⟨HNFil μ i, ⊤, lt_top_iff_ne_top.2 hi⟩ ⟨bot_le,le_top⟩ μ
      hμcvx)
    (HNFil μ (i + 1)) (HNFil_prop_of_def μ i hi).1 (HNFil μ (i + 1 + 1))
    ⟨le_of_lt <| lt_trans (HNFil_is_strict_mono μ i hi) hi', le_top⟩ hi'

open Classical in
/--
Uniqueness of the canonical Harder–Narasimhan filtration (`theorem3d10`).

Given any function `f : ℕ → ℒ` that:

* starts at `⊥` and eventually becomes constantly `⊤`,
* is strictly increasing up to its finite length,
* has semistable successive restrictions, and
* has strictly decreasing `μA`-slopes,

then `f` agrees pointwise with the canonical construction `HNFil μ`.

This is a key correctness statement: the filtration produced by the construction is
the unique one satisfying the expected axioms.
-/
theorem theorem3d10 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : ConvexI TotIntvl μ)
(f : ℕ → ℒ) (hf0 : f 0 = ⊥)
(hffin : ∃ n : ℕ, f n = ⊤)
(hfsi : ∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ Nat.find hffin → f i < f j)
(ffst : ∀ i : ℕ, i ≥ Nat.find hffin → f i = ⊤)
(hss : ∀ j : ℕ, (hj : j < Nat.find hffin) →
  Semistable (Resμ ⟨f j, f (j+1), hfsi j (j+1) (lt_add_one j) hj⟩ μ))
(hmua: ∀ i : ℕ, ∀ j : ℕ, (hij : i < j) → (hj : j < Nat.find hffin) →
  μA μ ⟨f i, f (i+1), hfsi i (i+1) (lt_add_one i) <| (by omega)⟩ >
  μA μ ⟨f j, f (j+1), hfsi j (j+1) (lt_add_one j) <| hj⟩)
: f = HNFil μ := by
  have hss := fun j hj ↦ (semistableI_iff μ ⟨f j, f (j+1), hfsi j (j+1) (lt_add_one j) hj⟩).2
    <| hss j hj
  let HNFilt := HNFil μ
  funext k
  induction k with
  | zero => simp only [hf0, HNFil]
  | succ n hn =>
  · by_cases h₁ : n + 1 ≤ Nat.find hffin
    · have h₂ : ∃ N : ℕ, N ≥ (n+1) ∧ HNFilt (n+1) ≤ f N :=
        ⟨Nat.find hffin, h₁, le_top.trans (ffst _ le_rfl).ge⟩
      let i : ℕ := Nat.find h₂
      have h₃ := HNFil_is_strict_mono μ n
        (hn ▸ Nat.find_min hffin (lt_of_lt_of_le (lt_add_one n) h₁))
      have h₁₅ : i ≥ n + 1 := (Nat.find_spec h₂).1
      have h₉ : i > 0 := Nat.zero_lt_of_lt h₁₅
      have hile : i ≤ Nat.find hffin := by
        by_contra! hc
        rcases not_and_or.1 (Nat.find_min h₂ hc) with c₁ | c₂
        · exact c₁ h₁
        · exact c₂ (le_top.trans (Nat.find_spec hffin).ge)
      have h₈ : i - 1 < Nat.find hffin := Nat.sub_one_lt_of_le h₉ hile
      have h₄ : ¬ HNFilt (n+1) ≤ f (i-1) := by
        rcases not_and_or.1 (Nat.find_min h₂ (Nat.sub_one_lt h₉.ne')) with h₅ | h₅
        · rw [show i - 1 = n by omega, hn]
          exact not_le_of_gt h₃
        · exact h₅
      have h₁₃ : HNFilt n ≤ f (i - 1) := by
        simp only [HNFilt, ← hn]
        rcases (Nat.le_sub_one_of_lt h₁₅).eq_or_lt with h₁₄ | h₁₄
        · rw [h₁₄]
        · exact (hfsi n (i-1) h₁₄ (by omega)).le
      have h₆ := impl.lem2d4₃I TotIntvl μ hμcvx (HNFilt (n + 1)) (in_TotIntvl (HNFilt (n + 1)))
        (f (i - 1)) (in_TotIntvl (f (i - 1))) h₄ (HNFilt n) <| le_inf (le_of_lt h₃) h₁₃
      have h₇ : f (i-1) < f i := hfsi (i - 1) i (Nat.sub_one_lt h₉.ne') hile
      have h₁₀ : μA μ ⟨HNFilt n, HNFilt (n+1), h₃⟩ ≤ μA μ ⟨f (i-1), f i, h₇⟩ := by
        have h₁₁ := hss (i-1) h₈
        simp only [Nat.sub_one_add_one h₉.ne'] at h₁₁
        exact le_trans h₆ <| le_of_not_gt (h₁₁.out.choose_spec.2.1 (HNFilt (n + 1) ⊔ f (i - 1))
          ⟨le_sup_right,sup_le_iff.2 ⟨(Nat.find_spec h₂).2,le_of_lt h₇⟩⟩
          <| ne_of_lt <|right_lt_sup.2 h₄)
      have hspec := (HNFil_prop_of_def μ n
        (ne_of_lt (lt_of_lt_of_le h₃ le_top))).1.out.choose_spec.choose_spec
      have h₁₂ : i = n + 1 := by
        refine eq_of_le_of_not_lt' h₁₅ ?_
        by_contra! hlt
        have hlt' : HNFilt n < f (n+1) := hn.ge.trans_lt (hfsi n (n+1) (lt_add_one n) h₁)
        have h₁₃ := hmua n (i-1) (Nat.lt_sub_of_add_lt hlt) h₈
        simp only [hn, Nat.sub_one_add_one h₉.ne', gt_iff_lt] at h₁₃
        exact hspec.1 (f (n+1)) ⟨le_of_lt hlt', le_top⟩ (ne_of_lt hlt')
          (lt_of_le_of_lt h₁₀ h₁₃)
      have h₁₄ := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg f h₁₂)
      have h₁₉ : HNFilt n < f (n+1) := lt_of_lt_of_le h₃ h₁₄
      have h₁₆ : f n < HNFilt (n + 1) := hn.le.trans_lt h₃
      have h₁₇ := le_of_not_gt <| (hss n h₁).out.choose_spec.choose_spec.1
        (HNFilt (n+1)) ⟨le_of_lt h₁₆,h₁₄⟩ <| ne_of_lt h₁₆
      simp only [hn] at h₁₇
      exact eq_of_le_of_ge (hspec.2 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ (ne_of_lt h₁₉)
        (eq_of_le_of_not_lt h₁₇ <| hspec.1 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ <|
          ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [ffst (n+1) (Nat.le_of_succ_le h₁),eq_comm]
      rw [ffst n (Nat.le_of_lt_succ h₁)] at hn
      have : ¬ n < HNlen μ := (HNFil_ne_top_iff_lt_len μ n).not.1 (not_ne_iff.2 hn.symm)
      exact not_ne_iff.1 <| (HNFil_ne_top_iff_lt_len μ (n+1)).not.2 (by omega)

section Fil_to_RelSeries
open Fin.NatCast

/--
Helper lemma: the underlying function of a `RelSeries (IntervalSemistableRel μ)` is
strictly monotone, obtained by forgetting the semistability witnesses to get an `LTSeries`.
-/
private lemma relSeries_strictMono {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
(s : RelSeries (IntervalSemistableRel μ)) : StrictMono s.toFun :=
  LTSeries.strictMono (s.map ⟨id, fun h ↦ h.choose⟩)

/--
Helper lemma: consecutive elements in a `RelSeries` are strictly increasing.

This extracts the `<` witness from the step relation, rewriting indices so it can be
used with `toFun` and standard arithmetic on `ℕ`.
-/
@[simp]
lemma relSeries_step_lt {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
(s : RelSeries (IntervalSemistableRel μ))
{i : ℕ} (hi : i + 1 < s.length)
 : s.toFun ↑i < s.toFun ↑(i + 1) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi.le (lt_add_one i))

/--
Helper lemma: the “next” consecutive inequality, shifted by one.

Together with `relSeries_step_lt`, this is used to express the slope comparison condition in
terms of `toFun` indices `i`, `i+1`, `i+2`.
-/
@[simp]
lemma relSeries_succ_step_lt {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : Intvl ℒ → S}
(s : RelSeries (IntervalSemistableRel μ))
{i : ℕ} (hi : i + 1 < s.length)
 : s.toFun ↑(i + 1) < s.toFun ↑(i + 2) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi (lt_add_one (i + 1)))

open Classical in
/--
Construct a `HarderNarasimhanFiltration` from a `RelSeries`.

Assuming `F1` starts at `⊥`, ends at `⊤`, and satisfies the strict slope decrease
condition expressed using `relSeries_step_lt`/`relSeries_succ_step_lt`, we build a
`HarderNarasimhanFiltration μ` whose underlying function agrees with `F1.toFun` up
to `F1.length`.

This is a bridge lemma used when switching between the “series” and “filtration”
presentations.
-/
lemma hHFil_of_hNSeries {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S)
(F1 : RelSeries (IntervalSemistableRel μ))
(h1 : F1.head = ⊥ ∧ F1.last = ⊤ ∧
  ∀ i : ℕ, (hi : i + 1 < F1.length) →
    ¬   μA μ ⟨F1.toFun i, F1.toFun ↑(i+1), relSeries_step_lt F1 hi⟩
      ≤ μA μ ⟨F1.toFun ↑(i+1), F1.toFun ↑(i+2), relSeries_succ_step_lt F1 hi⟩) :
∃ HN1 : HarderNarasimhanFiltration μ,
  HN1.filtration = (fun n ↦ if n ≤ F1.length then F1.toFun n else ⊤) ∧
                   (Nat.find HN1.fin_len = F1.length) := by
  let filtration1 := fun n ↦ if n ≤ F1.length then F1.toFun n else ⊤
  have hFtop : (if F1.length ≤ F1.length then F1.toFun ↑F1.length else ⊤) = ⊤ := by
    simp only [le_refl, ↓reduceIte, Fin.natCast_eq_last]
    exact h1.2.1
  have hstrange : ∃ n, (if n ≤ F1.length then F1.toFun ↑n else ⊤) = ⊤ := ⟨F1.length, hFtop⟩
  have Fmono : ∀ i j : ℕ, i < j → j ≤ F1.length → F1.toFun ↑i < F1.toFun ↑j :=
    fun _ _ hij hj ↦ relSeries_strictMono F1 (Fin.natCast_strictMono hj hij)
  have hslen : Nat.find hstrange = F1.length := by
      have hle := Nat.find_min' hstrange hFtop
      refine le_antisymm hle ?_
      by_contra! hc
      have t := Nat.find_spec hstrange
      rw [if_pos hle] at t
      exact absurd (t ▸ Fmono (Nat.find hstrange) F1.length hc le_rfl) not_top_lt
  let HN1 : HarderNarasimhanFiltration μ := {
      filtration := filtration1,
      monotone := by
        refine monotone_nat_of_le_succ fun n => ?_
        by_cases hn' : n + 1 ≤ F1.length
        · simp only [filtration1, Nat.le_of_succ_le hn', hn', ↓reduceIte]
          exact (Fmono n (n + 1) (lt_add_one n) hn').le
        · simp only [filtration1, hn', ↓reduceIte, le_top],
      first_eq_bot := by
        simp only [filtration1, zero_le, ↓reduceIte]
        exact h1.1,
      fin_len := hstrange,
      strict_mono := by
        intro i j hij hj
        rw [hslen] at hj
        simpa only [filtration1, (hij.trans_le hj).le, hj, ↓reduceIte] using Fmono i j hij hj,
      piecewise_semistable := by
        intro i hi
        rw [hslen] at hi
        have e₁ : filtration1 i = F1.toFun (Fin.castSucc ⟨i, hi⟩) := by
          simp only [filtration1, hi.le, ↓reduceIte, Fin.castSucc_mk,
            Fin.natCast_eq_mk (Nat.lt_add_right 1 hi)]
        have e₂ : filtration1 (i + 1) = F1.toFun (Fin.succ ⟨i, hi⟩) := by
          simp only [filtration1, show i + 1 ≤ F1.length from hi, ↓reduceIte, Fin.succ_mk,
            Fin.natCast_eq_mk (Nat.add_lt_add_right hi 1)]
        have hIJ : (⟨F1.toFun (Fin.castSucc ⟨i, hi⟩), F1.toFun (Fin.succ ⟨i, hi⟩),
            (F1.step ⟨i, hi⟩).choose⟩ : Intvl ℒ) = ⟨filtration1 i, filtration1 (i + 1),
            by rw [e₁, e₂]; exact (F1.step ⟨i, hi⟩).choose⟩ := Intvl.ext e₁.symm e₂.symm
        exact hIJ ▸ (F1.step ⟨i, hi⟩).choose_spec,
      μA_pseudo_strict_anti := by
        intro i hi
        unfold filtration1
        rw [hslen] at hi
        convert h1.2.2 i hi
        · simp only [(Nat.lt_of_succ_lt hi).le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [hi.le, ↓reduceIte]
        · simp only [show i + 2 ≤ F1.length from hi, ↓reduceIte]
    }
  exact ⟨HN1, rfl, hslen⟩

end Fil_to_RelSeries

end impl

end HarderNarasimhan
