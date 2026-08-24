/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.PayoffFunction.Semistable.Defs
import HarderNarasimhan.Interval
import HarderNarasimhan.PayoffFunction.SlopeLike
import HarderNarasimhan.PayoffFunction.NashEquilibrium
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
import HarderNarasimhan.JordanHolderFiltration.Defs
import HarderNarasimhan.PayoffFunction.SlopeLike
import HarderNarasimhan.PayoffFunction.GameValue
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.ModularLattice

/-!
  # Jordan–Hölder filtrations: internal implementation

  This file implements the construction and main internal properties of Jordan–Hölder
  filtrations.

  The core object is the recursively defined chain `JHFil μ ... : ℕ → ℒ`, built by
  repeatedly choosing a minimal element in a suitable set of candidates with constant
  total payoff. The lemmas `JHFil_step_payoff_eq_tot` and `JHFil_refine_lt_step_payoff`
  establish the defining step conditions of a `JordanHolderFiltration`.

  The middle part of the file develops a greedy subsequence-index construction (`subseqIdx`)
  for turning a chain that eventually hits `⊥` into a normalised chain starting at `⊤` and
  with strictly decreasing steps. The later lemmas connect the step conditions to
  semistability/stability of restricted slopes.

  Finally, under modularity (and affinity), the file proves the length-independence result
  via `induction_on_length_of_JordanHolderFiltration`.

  API note: this file is an internal implementation detail (most statements live in the
  `HarderNarasimhan.impl` namespace). For a stable user-facing interface, prefer importing
  `HarderNarasimhan.JordanHolderFiltration.Results`.
-/

namespace HarderNarasimhan

namespace impl

/- With the points type `↥I` now reducibly a `Subtype`, `Subtype.instDecidableEq` (fed by
`Classical.propDecidable`) would win over the bare classical instance in `Nat.find` occurrences
elaborated in this file, while the library lemmas quantified over an abstract lattice pick
`Classical.propDecidable` directly. Disable it locally so both elaborate identically. -/
attribute [-instance] Subtype.instDecidableEq

open Classical in
/-- `JHFil` is the recursive construction of the underlying chain of a Jordan–Hölder
  filtration.

  At step `k+1`, it looks for lattice elements `p` strictly between `⊥` and the previous
  value `JHFil ... k` such that `μ (⊥, p)` equals the total payoff `μ (⊥, ⊤)`. If there are
  any, it chooses a minimal one with respect to the well-founded order on `ℒ`; otherwise
  it falls back to `⊥`.

  The parameters include:
  * `hμ : μ (⊥, ⊤) ≠ ⊤` (finite total payoff),
  * slope-like and semistability hypotheses, and
  * a strengthened descending-chain condition `hdc` ensuring termination.
-/
noncomputable def JHFil
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S)
(hμ : μ ⊤ ≠ ⊤)
(hμsl : μ.IsSlopeLike) (hst : μ.IsSemistable)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) →
  ∃ N : ℕ, μ ⟨x (N +1), x N, sax <| lt_add_one N⟩ = ⊤) (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc n ∧ μ ⟨⊥, p,h⟩ =
      μ ⊤}
    if h𝒮 : 𝒮.Nonempty then
      (hacc.wf.has_min 𝒮 h𝒮).choose
    else
      ⊥



/-- `JHFil_anti_mono` shows that the constructed chain is strictly decreasing whenever the
  current value is above `⊥`.

  This is immediate from the choice of a minimal element in the defining set.
-/
lemma JHFil_anti_mono
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S)
(hμ : μ ⊤ ≠ ⊤)
(hμsl : μ.IsSlopeLike) (hst : μ.IsSemistable)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨x (N +1), x N, sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ, JHFil μ hμ hμsl hst hdc k > ⊥ →
  JHFil μ hμ hμsl hst hdc k > JHFil μ hμ hμsl hst hdc (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨⊥, p,h⟩ =
    μ ⊤}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simpa only [h]

open Classical in
/-- `JHFil_step_payoff_eq_tot` proves the first step condition for the chain `JHFil`.

  For each index `k` with `JHFil ... k > ⊥`, the payoff of the step
  `(JHFil ... (k+1), JHFil ... k)` is equal to the total payoff `μ (⊥, ⊤)`.
-/
lemma JHFil_step_payoff_eq_tot
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S)
(hμ : μ ⊤ ≠ ⊤)
(hμsl : μ.IsSlopeLike) (hst : μ.IsSemistable)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨x (N + 1), x N, sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → μ ⟨JHFil μ hμ hμsl hst hdc (k + 1),
  JHFil μ hμ hμsl hst hdc k,JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ = μ ⊤ := by
  intro k
  induction k with
  | zero =>
    intro hk'
    simp only [JHFil]
    by_cases this : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨⊥, p,h⟩ = μ ⊤}.Nonempty
    · simp only [this, ↓reduceDIte]
      let minTop := hacc.wf.has_min _ this
      have this' := minTop.choose_spec.1.2.2
      exact ((Or.resolve_left <| (Or.resolve_left <|
        hμsl.seesaw minTop.choose_spec.1.choose minTop.choose_spec.1.out.choose_spec.1)
        (by aesop)) (by aesop)).2.symm
    · simp only [this, ↓reduceDIte]
      rfl
  | succ k hk =>
    intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨⊥, p,h⟩ =
      μ ⊤}.Nonempty := by
      by_contra!
      simp only [JHFil,this, Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt,
        lt_self_iff_false] at hk'
    let min1 := hacc.wf.has_min _ jh_kp1_ntop
    have jh_kp1_ntop' : JHFil μ hμ hμsl hst hdc k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil,jh_kp1_ntop]
      exact min1.choose_spec.1.out.choose_spec.1
    have bot_jh_kp1_eq_ans := min1.choose_spec.1.2.2
    by_cases jh_kp2_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc (k + 1) ∧ μ ⟨⊥, p,h⟩
      = μ ⊤}.Nonempty
    · let min2 := hacc.wf.has_min _ jh_kp2_ntop
      have smart : μ ⟨⊥, min2.choose, min2.choose_spec.1.out.1⟩ =
          μ ⟨⊥, JHFil μ hμ hμsl hst hdc (k + 1), hk'⟩ := by
        rw [min2.choose_spec.1.out.choose_spec.2,← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop ]
        simp only [exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte]
      have hfinal : μ ⟨⊥, JHFil μ hμ hμsl hst hdc (k + 1), hk'⟩ =
        μ ⟨min2.choose, JHFil μ hμ hμsl hst hdc (k + 1),
        min2.choose_spec.1.out.choose_spec.1⟩ := by
        refine (Or.resolve_left ((Or.resolve_left <|
          hμsl.seesaw min2.choose_spec.1.out.choose min2.choose_spec.1.out.choose_spec.1)
          (?_)) (?_)).2
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]
          simp only [JHFil,jh_kp1_ntop]
          simp only [↓reduceDIte,
            exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
            lt_self_iff_false, not_false_eq_true]
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]
          simp only [JHFil,jh_kp1_ntop]
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
      simp only [JHFil,jh_kp1_ntop]
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
      have this': μ ⟨⊥, JHFil μ hμ hμsl hst hdc k, jh_kp1_ntop'⟩ = μ ⊤ := by
        by_cases hh : k = 0
        · simp only [hh,JHFil]
          rfl
        · have : JHFil μ hμ hμsl hst hdc k = JHFil μ hμ hμsl hst hdc ((k-1)+1) := by
            simp only [Nat.sub_one_add_one hh]
          simp only [this]
          have : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k-1) ∧ μ ⟨⊥, p, h⟩ =
            μ ⊤}.Nonempty := by
            by_contra hthis
            rw [this] at jh_kp1_ntop'
            simp only [JHFil,hthis] at jh_kp1_ntop'
            simp only [↓reduceDIte, gt_iff_lt, lt_self_iff_false] at jh_kp1_ntop'
          simp only [JHFil,this]
          simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
            forall_exists_index]
          simpa only [exists_and_left, Set.mem_ofPred_eq, gt_iff_lt, and_imp,
            forall_exists_index] using (hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.2
      simp only [← this']
      have : JHFil μ hμ hμsl hst hdc (k + 1) < JHFil μ hμ hμsl hst hdc k := by
        simpa only [JHFil, jh_kp1_ntop, ↓reduceDIte] using
          min1.choose_spec.1.out.choose_spec.1
      have this'' :  μ ⟨⊥, JHFil μ hμ hμsl hst hdc (k + 1), hk'⟩ = μ ⟨JHFil μ hμ hμsl hst hdc
        (k + 1), JHFil μ hμ hμsl hst hdc k, this⟩ := by
        rw [hk jh_kp1_ntop',← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
          forall_exists_index]
      exact ((Or.resolve_left <| (Or.resolve_left <| hμsl.seesaw hk' this)
        (fun this_1 ↦ ne_of_lt
        (lt_trans this_1.left this_1.right) this'')) (fun this_1 ↦ ne_of_lt
        (gt_trans this_1.1 this_1.2) (Eq.symm this''))).1



/-- `JHFil_fin_len` shows that the chain `JHFil` reaches `⊥` after finitely many steps.

  The proof uses the strengthened descending-chain condition `hdc` applied to the chain
  itself: if `⊥` were never reached, `hdc` would force a step payoff to be `⊤`, contradicting
  the finite-total-payoff assumption together with `JHFil_step_payoff_eq_tot`.
-/
lemma JHFil_fin_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S)
(hμ : μ ⊤ ≠ ⊤)
(hμsl : μ.IsSlopeLike) (hst : μ.IsSemistable)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨x (N +1), x N, sax <| lt_add_one N⟩ = ⊤) :
∃ N : ℕ, JHFil μ hμ hμsl hst hdc N = ⊥ := by
  by_contra! hc
  rcases hdc (fun n => JHFil μ hμ hμsl hst hdc n) <| strictAnti_of_add_one_lt <|
    fun n _ ↦ JHFil_anti_mono μ hμ hμsl hst hdc n (bot_lt_iff_ne_bot.2 <| hc n) with ⟨N, hN⟩
  exact hμ.symm <| hN ▸
    JHFil_step_payoff_eq_tot μ hμ hμsl hst hdc N (bot_lt_iff_ne_bot.2 <| hc N)

open Classical in
/-- `JHFil_refine_lt_step_payoff` proves the stability step condition for the chain `JHFil`.

  For each `k` with `JHFil ... k > ⊥` and any strict intermediate `z` between
  `JHFil ... (k+1)` and `JHFil ... k`, the payoff strictly decreases when refining the step
  through `z`.
-/
lemma JHFil_refine_lt_step_payoff
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) [hsdcc' : StrongDescendingChainCondition' μ]
(hμ : μ ⊤ ≠ ⊤)
(hμsl : μ.IsSlopeLike) (hst : μ.IsSemistable)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨x (N +1), x N, sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → ∀ z : ℒ, (h' : JHFil μ hμ hμsl hst hdc (k + 1) < z)
  → (h'' : z < JHFil μ hμ hμsl hst hdc k) →
  μ ⟨JHFil μ hμ hμsl hst hdc (k + 1), z, h'⟩ < μ ⟨JHFil μ hμ hμsl hst hdc (k + 1),
    JHFil μ hμ hμsl hst hdc k, JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ := by
  intro k hk z h' h''
  have this_new : μmax μ ⊤ = μ ⊤ :=
    PayoffFunction.max_top_eq_apply_iff.2
      (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
  have this_q : μ ⟨⊥, z, lt_of_le_of_lt bot_le h'⟩ ≤ μ ⊤ :=
    this_new ▸ le_iSup₂_of_le z ⟨lt_of_le_of_lt bot_le h', le_top⟩ le_rfl
  by_cases hfp1bot : JHFil μ hμ hμsl hst hdc (k + 1) = ⊥
  · simp only [hfp1bot]
    have : ¬ {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨⊥, p, h⟩ =
      μ ⊤}.Nonempty := by
      by_contra!
      simp only [JHFil,this] at hfp1bot
      have := (hacc.wf.has_min _ this).choose_spec.1.out.choose
      simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, and_imp,
        forall_exists_index] at hfp1bot
      simp only [exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index] at this
      exact (ne_of_lt this) hfp1bot.symm
    replace this := Set.eq_empty_iff_forall_notMem.1 (Set.not_nonempty_iff_eq_empty.1 this) z
    simp only [exists_and_left, Set.mem_ofPred_eq, not_and, not_exists] at this
    replace := lt_of_le_of_ne this_q <| this h'' (lt_of_le_of_lt bot_le h')
    by_cases hk' : k = 0
    · simpa only [hk',JHFil]
    · conv_rhs =>
        arg 2; arg 2; arg 6
        rw [← Nat.sub_one_add_one hk']
      have hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k - 1) ∧ μ ⟨⊥, p, h⟩ =
        μ ⊤}.Nonempty := by
        by_contra!
        have this' : JHFil μ hμ hμsl hst hdc k = JHFil μ hμ hμsl hst hdc ((k-1)+1) :=
          congrArg (JHFil μ hμ hμsl hst hdc) (Nat.sub_one_add_one hk').symm
        simp only [this',JHFil,this] at hk
        simp only [Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt, lt_self_iff_false] at hk
      rw [← (hacc.wf.has_min _ hne).choose_spec.1.out.2.2] at this
      simp only [JHFil,hne]
      simp only [↓reduceDIte, exists_and_left, Set.mem_ofPred_eq, gt_iff_lt, and_imp,
        forall_exists_index]
      simpa only [exists_and_left, Set.mem_ofPred_eq,
        gt_iff_lt, and_imp, forall_exists_index] using this
  · have h''' : μ ⟨⊥, z, lt_of_le_of_lt bot_le h'⟩ < μ ⊤ := by
      refine lt_of_le_of_ne this_q ?_
      by_contra!
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧
        μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
      · have := (hacc.wf.has_min _ hne).choose_spec.2 z (by use lt_of_le_of_lt bot_le h')
        simp only [JHFil,hne] at h'
        simp only [gt_iff_lt, exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this h'
      · exact hne ⟨z, lt_of_le_of_lt bot_le h', h'', this⟩
    have h'''' : μ ⊤ = μ ⟨⊥, JHFil μ hμ hμsl hst hdc (k + 1),
      bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨⊥, p, h⟩ =
        μ ⊤}.Nonempty
      · simp only [JHFil,hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp only [gt_iff_lt, exists_and_left, Set.mem_ofPred_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this.symm
      · simp only [JHFil,hne] at hfp1bot
        simp only [↓reduceDIte, not_true_eq_false] at hfp1bot
    exact (JHFil_step_payoff_eq_tot μ hμ hμsl hst hdc k hk).symm ▸ lt_trans ((Or.resolve_right <|
      (Or.resolve_left <| hμsl.seesaw (bot_lt_iff_ne_bot.2 hfp1bot) h')
      (not_and_iff_not_or_not.2 <| Or.inl <| not_lt_of_gt <|
      h'''' ▸ h''')) (not_and_iff_not_or_not.2 <| Or.inl <| ne_of_gt <| h'''' ▸ h''')).2 h'''

open Classical in
/-- `JH_pos_len` is a small normalisation lemma: any Jordan–Hölder filtration has
  positive length (i.e. its `fin_len` witness cannot be `0`) because the filtration starts
  at `⊤`.
-/
lemma JH_pos_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : PayoffFunction ℒ S} : ∀ JH : JordanHolderFiltration μ, JH.length ≠ 0 := by
  intro JH h
  have := JH.filtration_length
  rw [h, JH.first_eq_top] at this
  exact top_ne_bot this

/-/ `exists_next_lt` is the existence input for `Nat.find` in `subseqIdx`: for an antitone `f`
that eventually hits `⊥`, from any index `n` with `f n ≠ ⊥` there is a later index where `f`
drops strictly.
-/
private lemma exists_next_lt {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (n : ℕ) (hcond : f n ≠ ⊥) :
  ∃ k : ℕ, n < k ∧ f k < f n := by
  let m := max (n + 1) atf.choose
  refine ⟨m, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _), ?_⟩
  have hm : f m = ⊥ := le_bot_iff.mp <| atf.choose_spec ▸ hf (le_max_right _ _)
  simpa [hm] using bot_lt_iff_ne_bot.2 hcond

open Classical in
/-/ `subseqIdx f atf hf` is the greedy index sequence underlying the normalised subsequence.

It records which indices of the original chain are kept. At each step, if the current selected
value is already `⊥`, we advance the index by one to keep a genuine subsequence map `ℕ → ℕ`; if
not, we jump to the first later index where the value drops strictly.
-/
noncomputable def subseqIdx {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      if hcond : f (subseqIdx f atf hf t) = ⊥ then subseqIdx f atf hf t + 1
      else Nat.find (exists_next_lt f atf hf (subseqIdx f atf hf t) hcond)

/-/ `subseqIdx.next_exists` packages the witness that, as long as the current selected value is
not `⊥`, there is a later index where `f` drops strictly.
-/
private lemma subseqIdx.next_exists {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (t : ℕ)
  (hcond : f (subseqIdx f atf hf t) ≠ ⊥) :
  ∃ k : ℕ, subseqIdx f atf hf t < k ∧ f k < f (subseqIdx f atf hf t) :=
  exists_next_lt f atf hf (subseqIdx f atf hf t) hcond

open Classical in
private lemma subseqIdx.succ_eq_find {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (t : ℕ)
  (hcond : f (subseqIdx f atf hf t) ≠ ⊥) :
  subseqIdx f atf hf (t + 1) = Nat.find (subseqIdx.next_exists f atf hf t hcond) := by
  simp [subseqIdx, hcond]

open Classical in
private lemma subseqIdx.lt_succ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (t : ℕ) :
  subseqIdx f atf hf t < subseqIdx f atf hf (t + 1) := by
  by_cases hcond : f (subseqIdx f atf hf t) = ⊥
  · simp [subseqIdx, hcond]
  · rw [subseqIdx.succ_eq_find f atf hf t hcond]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hf t hcond)).1

private lemma subseqIdx.ge_self {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
  ∀ n : ℕ, n ≤ subseqIdx f atf hf n :=
  (strictMono_nat_of_lt_succ (subseqIdx.lt_succ f atf hf)).id_le

open Classical in
private lemma subseqIdx.const_between {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (i m : ℕ)
  (hleft : subseqIdx f atf hf i ≤ m) (hright : m < subseqIdx f atf hf (i + 1)) :
  f m = f (subseqIdx f atf hf i) := by
  by_cases hbot : f (subseqIdx f atf hf i) = ⊥
  · have hs : subseqIdx f atf hf (i + 1) = subseqIdx f atf hf i + 1 := by
      simp [subseqIdx, hbot]
    have hm : m = subseqIdx f atf hf i := by omega
    simp [hm]
  · have hs := subseqIdx.succ_eq_find f atf hf i hbot
    have hle : f m ≤ f (subseqIdx f atf hf i) := hf hleft
    apply eq_of_le_of_not_lt hle
    intro hlt
    by_cases hm : m = subseqIdx f atf hf i
    · simp [hm] at hlt
    · have hm' : subseqIdx f atf hf i < m := lt_of_le_of_ne hleft fun hm' => hm hm'.symm
      have hfind := Nat.find_min' (subseqIdx.next_exists f atf hf i hbot) ⟨hm', hlt⟩
      omega

/-- `subseqIdx_hits_bot` shows that the values selected by `subseqIdx f atf` eventually reach `⊥`.

  Concretely, it produces an index `N` with `f (subseqIdx f atf hf N) = ⊥`.
-/
lemma subseqIdx_hits_bot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ)
  (atf : ∃ k, f k = ⊥) (hf : Antitone f) (_hf0 : f 0 = ⊤) :
  ∃ N : ℕ, f (subseqIdx f atf hf N) = ⊥ :=
  ⟨atf.choose, le_bot_iff.mp <|
    le_of_le_of_eq (hf (subseqIdx.ge_self f atf hf atf.choose)) atf.choose_spec⟩

open Classical in
/-- `subseqIdx_strictAnti` is the strict-decrease property for the values selected by `subseqIdx`.

  Up to the index where `f (subseqIdx f atf ..)` first hits `⊥`, consecutive selected values are
  strictly decreasing. This is the key fact used later to turn antitonicity into a `StrictAnti`
  chain.
-/
lemma subseqIdx_strictAnti {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f) :
∀ (i j : ℕ), i < j → j ≤ Nat.find (subseqIdx_hits_bot f atf hfat hf0) →
  f (subseqIdx f atf hfat j) < f (subseqIdx f atf hfat i) := by
  intro i j hij hj
  have hbot : f (subseqIdx f atf hfat i) ≠ ⊥ :=
    Nat.find_min (subseqIdx_hits_bot f atf hfat hf0) (lt_of_lt_of_le hij hj)
  refine lt_of_le_of_lt
    (hfat ((strictMono_nat_of_lt_succ (subseqIdx.lt_succ f atf hfat)).monotone hij)) ?_
  rw [subseqIdx.succ_eq_find f atf hfat i hbot]
  exact (Nat.find_spec (subseqIdx.next_exists f atf hfat i hbot)).2

open Classical in
/-- `subseqIdx_find_ne_of_plateau` is a technical combinatorial lemma about the index where
`f (subseqIdx ...)` hits `⊥`.

  It shows that this index cannot coincide with a specified `k` under a mild “plateau” hypothesis
  (`∃ N, N+1 ≤ k ∧ f N = f (N+1)`). The proof uses a finite-cardinality argument on the image set
  `{f t | t ≤ k}`.
-/
lemma subseqIdx_find_ne_of_plateau {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f) (k : ℕ) (hk : f k = ⊥)
(htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N + 1)) :
  (Nat.find <| subseqIdx_hits_bot f atf hfat hf0) ≠ k := by
  let A := Nat.find <| subseqIdx_hits_bot f atf hfat hf0
  let 𝒮 := {f t | (t ≤ k)}
  have helper : ∀ t : ℕ, ∃ l : ℕ, l ≤ k ∧ f (subseqIdx f atf hfat t) = f l := by
    intro t
    if hcond : f (subseqIdx f atf hfat t) = ⊥ then exact ⟨k,⟨le_rfl,hcond ▸ hk.symm⟩⟩
    else
      refine ⟨subseqIdx f atf hfat t, ?_, rfl⟩
      by_contra hlt
      exact hcond <| le_bot_iff.mp <| hk ▸ hfat (le_of_lt (lt_of_not_ge hlt))
  let Φ : Fin (A+1) → 𝒮 := fun d ↦
    let l := (helper d).choose
    let hl := (helper d).choose_spec
    ⟨f (subseqIdx f atf hfat d), Set.mem_ofPred.mpr ⟨l, ⟨hl.1, hl.2.symm⟩⟩⟩
  have hΦ : Function.Injective Φ := by
    intro d1 d2 h
    have this : f (subseqIdx f atf hfat d1) = f (subseqIdx f atf hfat d2) :=
      congrArg Subtype.val h
    if hd : d1 < d2 then
      have hlt' := subseqIdx_strictAnti f hf0 atf hfat d1 d2 hd (Fin.is_le d2)
      simp [this] at hlt'
    else
      if hd' : d2 < d1 then
        have hlt' := subseqIdx_strictAnti f hf0 atf hfat d2 d1 hd' (Fin.is_le d1)
        simp [this] at hlt'
      else exact Fin.le_antisymm (le_of_not_gt hd') (le_of_not_gt hd)
  let fS : Fin (k+1) → 𝒮 := fun n ↦ ⟨f n,Set.mem_ofPred.mpr ⟨n,⟨Fin.is_le n,rfl⟩⟩⟩
  have fSsuj : Function.Surjective fS := by
    intro y
    rcases y.prop.out with ⟨n1,n2,n3⟩
    use ⟨n1,Nat.lt_succ_of_le n2⟩, SetCoe.ext n3
  have : Fintype 𝒮 :=  Set.Finite.fintype <| Finite.of_surjective fS fSsuj
  have ineq1: A + 1 ≤ Fintype.card ↑𝒮 := Fintype.card_fin (A+1) ▸ Fintype.card_le_of_injective Φ hΦ
  have ineq2 : Fintype.card ↑𝒮 < k + 1 := Fintype.card_fin (k+1) ▸
    Fintype.card_lt_of_surjective_not_injective fS fSsuj <| Function.not_injective_iff.mpr
    ⟨⟨htech.choose,Nat.lt_add_right 1 htech.choose_spec.1⟩, ⟨htech.choose+1,Nat.add_lt_add_right
    htech.choose_spec.1 1⟩,⟨SetCoe.ext htech.choose_spec.2,by simp⟩⟩
  exact ne_of_lt <| Nat.succ_lt_succ_iff.mp <| lt_of_le_of_lt ineq1 ineq2

open Classical in
/-- `subseqIdx_inherit_step_predicate` transports a stepwise predicate from the original chain to
the values selected by `subseqIdx`.

  Given a predicate `P` on strict steps of `f` (assumed for each `i < Nat.find atf`), the lemma
  produces the corresponding fact for each strict step of the selected values before they reach
  `⊥`.
-/
lemma subseqIdx_inherit_step_predicate {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f)
(P : StrictIntvl ℒ → Prop)
(ho : ∀ i : ℕ, i < Nat.find atf → (hfi :f (i + 1) < f i) → P ⟨f (i+1), f i,hfi⟩) :
∀ i : ℕ, (hi : i < Nat.find (subseqIdx_hits_bot f atf hfat hf0)) →
  P ⟨f (subseqIdx f atf hfat (i + 1)), f (subseqIdx f atf hfat i),
    subseqIdx_strictAnti f hf0 atf hfat i (i + 1) (Nat.lt_succ_self i) (Nat.succ_le_iff.2 hi)⟩ := by
  intro i hi
  have hbot : f (subseqIdx f atf hfat i) ≠ ⊥ :=
    Nat.find_min (subseqIdx_hits_bot f atf hfat hf0) hi
  let n := subseqIdx f atf hfat (i + 1)
  have hn : subseqIdx f atf hfat i < n := by
    dsimp [n]
    rw [subseqIdx.succ_eq_find f atf hfat i hbot]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hfat i hbot)).1
  have hstep : f n < f (subseqIdx f atf hfat i) := by
    dsimp [n]
    rw [subseqIdx.succ_eq_find f atf hfat i hbot]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hfat i hbot)).2
  have hpred_eq : f (n - 1) = f (subseqIdx f atf hfat i) := by
    apply subseqIdx.const_between f atf hfat i (n - 1)
    repeat omega
  have hpred_lt : f n < f (n - 1) := by rwa [hpred_eq]
  have hpred_bd : n - 1 < Nat.find atf := by
    by_contra hge
    have hbot_pred : f (n - 1) = ⊥ := le_bot_iff.mp <| (Nat.find_spec atf) ▸ hfat (le_of_not_gt hge)
    have hbot_n : f n = ⊥ :=
      le_bot_iff.mp <| (Nat.find_spec atf) ▸ hfat (le_trans (le_of_not_gt hge) (Nat.sub_le n 1))
    exact (lt_self_iff_false ⊥).mp (hbot_n ▸ hbot_pred ▸ hpred_lt)
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ i) (subseqIdx.ge_self f atf hfat (i + 1))
  have hpred_lt' : f ((n - 1) + 1) < f (n - 1) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)] using hpred_lt
  convert ho (n - 1) hpred_bd hpred_lt' using 1
  simp [n, hpred_eq, Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)]

/-- `μA_eq_μmin` is a small bridge lemma between two “minimal slope” constructions.

  It rewrites `μmin μ I` as the value `μA μ I` by applying Proposition 4.1 to the restricted slope
  `Resμ I μ`.
-/
lemma μA_eq_μmin {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S)
[μ.IsSlopeLike] (I : StrictIntvl ℒ) :
μmin μ I = μA μ I := by
  convert Eq.symm <| (show μAstar (Resμ I μ) = μmin (Resμ I μ) ⊤ from
    PayoffFunction.A_top_eq_min_top)
  · simpa only [μmin_res_intvl] using by rfl
  · simpa only [μAstar, μA_res_intvl] using by rfl

open Classical in
/-- `μ_bot_JH_eq_μ_tot` is an invariance statement along a Jordan–Hölder filtration.

  For every index `i` before the terminal length, the payoff `μ (⊥, JH.filtration i)` equals the
  total payoff `μ (⊥, ⊤)`. The proof is by induction on `i` using the first step condition.
-/
lemma μ_bot_JH_eq_μ_tot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : PayoffFunction ℒ S}
[hsl : μ.IsSlopeLike] (JH : JordanHolderFiltration μ) :
∀ i : ℕ, (hi : i < JH.length) → μ ⟨⊥, JH.filtration i, by
  rw [← JH.filtration_length]
  exact JH.strict_anti hi.le (le_rfl : JH.length ≤ _) hi
  ⟩ = μ ⊤ := by
  intro i hi
  induction i with
  | zero => simp only [JH.first_eq_top, StrictIntvl.mk_bot_top]
  | succ i hi' =>
    refine ((hsl.seesaw_total_eq_right_iff
      (JH.filtration_length ▸ JH.strict_anti hi.le (le_rfl : JH.length ≤ _) hi)
      (JH.first_eq_top ▸ JH.strict_anti (Nat.zero_le _) (le_of_lt hi)
        (Nat.zero_lt_succ i))).1 ?_)
    simp only [StrictIntvl.mk_bot_top]
    rw [← JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]
    if htop : JH.filtration i = ⊤ then
      simp only [htop]
    else
    refine ((hsl.seesaw_left_eq_right_iff
      (JH.strict_anti (Nat.le_of_succ_le hi.le) (Nat.le_of_succ_le hi) (lt_add_one i))
      (Ne.lt_top htop)).1 ?_)
    specialize hi' (Nat.lt_of_succ_lt hi)
    rw [← ((hsl.seesaw_total_eq_right_iff
        (JH.filtration_length ▸ JH.strict_anti (Nat.lt_of_succ_lt hi).le
          (le_rfl : JH.length ≤ _) (Nat.lt_of_succ_lt hi))
        (Ne.lt_top htop)).2 hi'), JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]
    rfl

open Classical in
/-- `semistable_of_step_cond₂` turns a strict step condition into semistability on each step.

  Assuming that for every intermediate `z` strictly between consecutive values
  `filtration (i+1) < z < filtration i` the slope strictly improves, the restricted slope
  `Resμ ⟨filtration (i+1), filtration i, _⟩ μ` is semistable.
-/
lemma semistable_of_step_cond₂
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) [μ.IsSlopeLike] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨filtration (i+1), z, h'⟩ < μ ⟨filtration (i+1), filtration i,
      strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) →
  PayoffFunction.IsSemistable (Resμ ⟨filtration (i+1), filtration i,
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
  intro h i hi
  apply PayoffFunction.isSemistable_of_hasNashEquilibrium (fun _ _ ↦ inferInstance)
    (fun _ _ ↦ inferInstance)
  apply PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.1
  apply PayoffFunction.min_top_eq_apply_iff.1
  apply eq_of_le_of_ge ?_ ?_
  · exact iInf₂_le ⊥ ⟨le_rfl, bot_lt_top⟩
  · refine le_iInf₂ fun u hu1 ↦ ?_
    simp only [μ_res_intvl]
    if hu : u = ⊥ then
      subst hu
      exact le_rfl
    else
    have hul : filtration (i + 1) < u.val :=
      lt_of_le_of_ne u.prop.1 fun hc ↦ hu <| Subtype.coe_inj.1 hc.symm
    have hur : u.val < filtration i :=
      lt_of_le_of_ne u.prop.2 fun hc ↦ hu1.2.ne <| Subtype.coe_inj.1 hc
    exact le_of_lt <| ((inferInstance : μ.IsSlopeLike).seesaw_total_lt_right_iff hul hur).2
      (h i hi u.val hul hur)

open Classical in
/-- `stable_of_step_cond₂` upgrades the previous lemma from semistability to stability.

  Under the same strict step condition, each restricted slope on a step interval is not only
  semistable but satisfies the strict inequality required for `Stable`.
-/
lemma stable_of_step_cond₂
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) [μ.IsSlopeLike] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨filtration (i+1), z, h'⟩ < μ ⟨filtration (i+1), filtration i,
      strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) →
  PayoffFunction.IsStable (Resμ ⟨filtration (i+1), filtration i,
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
    intro h i hi
    refine {
      toIsSemistable := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi,
      ne := ?_ }
    · intro x hx hx'
      let stepI : StrictIntvl ℒ :=
        ⟨filtration (i + 1), filtration i, strict_anti i (i + 1) (lt_add_one i) hi⟩
      have hx_left : filtration (i + 1) < x.val :=
        lt_of_le_of_ne x.prop.1 fun hc ↦ hx.ne' <| Subtype.coe_inj.1 hc.symm
      change μA (Resμ stepI μ) ⟨⊥, x, hx⟩ ≠ μA (Resμ stepI μ) ⊤
      have hAstar_step : μAstar (Resμ stepI μ) = μmin (Resμ stepI μ) ⊤ :=
        PayoffFunction.A_top_eq_min_top
      have hAstar_x : μAstar (Resμ ⟨filtration (i + 1), x.val, hx_left⟩ μ) =
          μmin (Resμ ⟨filtration (i + 1), x.val, hx_left⟩ μ) ⊤ :=
        PayoffFunction.A_top_eq_min_top
      simp only [μAstar, μA_res_intvl,μmin_res_intvl] at *
      rw [hAstar_step]
      replace hAstar_x : μA μ (StrictIntvl.ofSub ⟨⊥, x, hx⟩) =
        μmin μ (StrictIntvl.ofSub ⟨⊥, x, hx⟩) := hAstar_x
      rw [hAstar_x]
      have hss := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi
      have hNash_step := hss.hasNashEquilibrium
      have hμmin_step : μmin (Resμ stepI μ) ⊤ = (Resμ stepI μ) ⊤ :=
        PayoffFunction.min_top_eq_apply_iff.2
          (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
      simp only [μmin_res_intvl,μ_res_intvl] at hμmin_step
      rw [hμmin_step]
      exact ne_of_lt <| lt_of_le_of_lt
        (PayoffFunction.min_le_apply (μ := μ) (I := ⟨filtration (i + 1), ↑x, hx_left⟩)) <|
        h i hi x.val hx_left hx'

open Classical in
/-- `step_cond₂_of_stable` is the converse direction: stability implies the strict step condition.

  If each restricted slope on the step intervals is stable, then for every strict intermediate
  `z` one has the strict inequality comparing `μ (filtration (i+1), z)` with the step value.
-/
lemma step_cond₂_of_stable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : PayoffFunction ℒ S) [μ.IsSlopeLike] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i):
(
∀ i : ℕ, (hi : i < Nat.find fin_len) →
  PayoffFunction.IsStable (Resμ ⟨filtration (i+1), filtration i,
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
)
→ (∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨filtration (i+1), z, h'⟩ < μ ⟨filtration (i+1), filtration i,
      strict_anti i (i+1) (lt_add_one i) hi⟩
) := by
  intro hst i hi z hz hz'
  let stepI : StrictIntvl ℒ :=
    ⟨filtration (i + 1), filtration i, strict_anti i (i + 1) (lt_add_one i) hi⟩
  let midI : ↥stepI := ⟨z, le_of_lt hz, le_of_lt hz'⟩
  have hmid_ne_bot : ⊥ < midI := bot_lt_iff_ne_bot.2 fun hc ↦ ne_of_gt hz (congrArg Subtype.val hc)
  have hmid_ne_top : midI < ⊤ := lt_top_iff_ne_top.2 fun hc ↦ ne_of_lt hz' (congrArg Subtype.val hc)
  have hss := (hst i hi).toIsSemistable.not_lt midI hmid_ne_bot
  simp only [not_lt] at hss
  have hst' : μA (Resμ stepI μ) ⟨⊥, midI, hmid_ne_bot⟩ < μA (Resμ stepI μ) ⊤ :=
    lt_of_le_of_ne hss ((hst i hi).ne midI hmid_ne_bot hmid_ne_top)
  have hAstar_step : μA (Resμ stepI μ) ⊤ = μmin (Resμ stepI μ) ⊤ :=
    PayoffFunction.A_top_eq_min_top
  rw [hAstar_step] at hst'
  have hAstar_mid : μA (Resμ ⟨filtration (i + 1), z, hz⟩ μ) ⊤ =
      μmin (Resμ ⟨filtration (i + 1), z, hz⟩ μ) ⊤ :=
    PayoffFunction.A_top_eq_min_top
  have hb : μA (Resμ ⟨filtration (i + 1), filtration i, gt_trans hz' hz⟩ μ)
    ⟨⊥, midI, hmid_ne_bot⟩ =
    μA (Resμ ⟨filtration (i + 1), z, hz⟩ μ) ⊤ := by
    simp only [μA_res_intvl,μmin_res_intvl] at *
    rfl
  rw [hb, hAstar_mid] at hst'
  have hNash_step := (hst i hi).toIsSemistable.hasNashEquilibrium
  have hμmin_step : μmin (Resμ stepI μ) ⊤ = (Resμ stepI μ) ⊤ :=
    PayoffFunction.min_top_eq_apply_iff.2
      (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  rw [hμmin_step] at hst'
  have hμmax_step : μmax (Resμ stepI μ) ⊤ = (Resμ stepI μ) ⊤ :=
    PayoffFunction.max_top_eq_apply_iff.2
      (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2 hNash_step)
  simp only [μmin_res_intvl,μ_res_intvl] at hst'
  have hsSup_step : ∀ (u : ↥stepI) (hu : (⊥ : ↥stepI) < u),
      Resμ stepI μ ⟨⊥, u, hu⟩ ≤ Resμ stepI μ ⊤ := fun u hu ↦
    hμmax_step ▸ le_iSup₂_of_le u ⟨hu, le_top⟩ le_rfl
  have hsSup_step_bak := hsSup_step
  have hsSup_mid := hsSup_step midI hmid_ne_bot
  have hsSup_mid' : μ ⟨filtration (i + 1), z, hz⟩ ≤ μ ⟨filtration (i + 1), filtration i,
      strict_anti i (i + 1) (lt_add_one i) hi⟩ := hsSup_mid
  refine lt_of_le_of_ne hsSup_mid' ?_
  by_contra hc
  replace hst' : μmin μ ⟨filtration (i + 1), z, hz⟩ <
      μ ⟨filtration (i + 1), filtration i, gt_trans hz' hz⟩ := hst'
  rw [← hc] at hst'
  obtain ⟨y, hy⟩ := iInf_lt_iff.1 hst'
  obtain ⟨hy1, hs⟩ := iInf_lt_iff.1 hy
  have := ((inferInstance : μ.IsSlopeLike).seesaw_right_lt_total_iff
    (x := filtration (i + 1)) (y := y) (z := z)
    (lt_of_le_of_ne hy1.1 fun hc ↦ by simp only [hc, lt_self_iff_false] at hs)
    hy1.2).1 hs
  simp only [hc] at this
  have res := hsSup_step_bak ⟨y, hy1.1, le_of_lt <| lt_of_le_of_lt hy1.2.le hz'⟩ (by
    refine lt_of_le_of_ne hy1.1 ?_
    by_contra hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    simp only [← hc, StrictIntvl.val_bot, stepI, lt_self_iff_false] at hs)
  simp only [stepI, μ_res_intvl] at res
  exact (not_le_of_gt this) res

open Classical in
/-- `semistable_resμ_of_jordanHolderFiltration` deduces semistability for the final restriction.

  If the last nontrivial step of a Jordan–Hölder filtration lies strictly below `⊤`, then the
  restricted slope on the interval `(JH.filtration (len-1), ⊤)` is semistable.
-/
lemma semistable_resμ_of_jordanHolderFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : PayoffFunction ℒ S}
[FiniteTotalPayoff μ] [μ.IsSlopeLike] [μ.IsSemistable]
[StrongDescendingChainCondition' μ] [μ.IsAffine] (JH : JordanHolderFiltration μ)
(h : JH.filtration (JH.length - 1) < ⊤) :
PayoffFunction.IsSemistable (Resμ ⟨JH.filtration (JH.length - 1), ⊤,h⟩ μ) := by
  apply PayoffFunction.isSemistable_of_hasNashEquilibrium (fun _ _ ↦ inferInstance)
    (fun _ _ ↦ inferInstance)
  apply PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.1
  apply PayoffFunction.min_top_eq_apply_iff.1
  change μmin (Resμ ⟨JH.filtration (JH.length - 1), ⊤, h⟩ μ) ⊤ =
    (Resμ ⟨JH.filtration (JH.length - 1), ⊤, h⟩ μ) ⊤
  rw [μmin_res_intvl, μ_res_intvl]
  apply eq_of_le_of_ge ?_ ?_
  · exact iInf₂_le (JH.filtration (JH.length - 1)) ⟨le_rfl, h⟩
  · refine le_iInf₂ fun u hu1 ↦ ?_
    have : μmin μ ⊤ = μ ⊤ :=
      PayoffFunction.min_top_eq_apply_iff.2
        (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2
          (PayoffFunction.IsSemistable.hasNashEquilibrium inferInstance))
    have this' : μ ⟨u, ⊤, lt_top_iff_ne_top.2 hu1.2.ne⟩ ≥ μ ⊤ := by
      rw [← this]
      exact iInf₂_le u ⟨bot_le, hu1.2⟩
    replace := μ_bot_JH_eq_μ_tot JH (JH.length - 1) (Nat.sub_one_lt <| JH_pos_len JH)
    have hEq := ((inferInstance : μ.IsSlopeLike).seesaw_total_eq_right_iff
      (bot_lt_iff_ne_bot.2 <| JH.ne_bot_of_lt_length <| Nat.sub_one_lt <| JH_pos_len JH)
      h).2 this
    rw [StrictIntvl.mk_bot_top] at hEq
    rwa [hEq] at this'

open Classical in
/-- `induction_on_length_of_JordanHolderFiltration` is the main internal induction principle.

  Fix `n`. Assuming there exists a Jordan–Hölder filtration of length `≤ n`, the lemma shows that
  every Jordan–Hölder filtration for the same slope function has length `≤ n`.

  This is proved by induction on `n`, using restriction to a final interval and modularity to
  compare lengths.
-/
lemma induction_on_length_of_JordanHolderFiltration (n : ℕ) :
    ∀ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
      [WellFoundedGT ℒ] [IsModularLattice ℒ]
      {S : Type*} [CompleteLinearOrder S]
      {μ : PayoffFunction ℒ S}
      [FiniteTotalPayoff μ] [μ.IsSlopeLike] [μ.IsSemistable]
      [StrongDescendingChainCondition' μ] [μ.IsAffine],
      (∃ JH : JordanHolderFiltration μ, JH.length ≤ n) →
      ∀ JH' : JordanHolderFiltration μ, JH'.length ≤ n := by
  induction n with
  | zero =>
    intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hsdcc' affine ⟨JH,hJH⟩ JH'
    exact absurd (nonpos_iff_eq_zero.mp hJH) (JH_pos_len JH)
  | succ n hn =>
    intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hsdcc' affine ⟨JHy,hJHy⟩ JHx
    let lenx := JHx.length
    let leny := JHy.length
    let x0 := JHx.filtration (lenx - 1)
    if htriv : lenx = 1 then exact htriv ▸ Nat.le_add_left 1 n
    else
    have hlenx_ne_zero : lenx ≠ 0 := JH_pos_len JHx
    have hlenx : 0 < lenx - 1 := by omega
    let Ires : StrictIntvl ℒ :=
      ⟨x0, ⊤, (JHx.first_eq_top) ▸ JHx.strict_anti (Nat.zero_le _) (Nat.sub_le lenx 1) hlenx⟩
    have hx0_bot : ⊥ < x0 :=
      bot_lt_iff_ne_bot.2 <| JHx.ne_bot_of_lt_length <| Nat.sub_one_lt <| JH_pos_len JHx
    have nt : x0 < ⊤ :=
      JHx.first_eq_top ▸ JHx.strict_anti (Nat.zero_le _) (Nat.sub_le lenx 1) hlenx
    have hlast_step := JHx.step_cond₁ (lenx - 1) (Nat.sub_one_lt (JH_pos_len JHx))
    have hstepx0 : μ ⟨x0, ⊤, nt⟩ = μ ⊤ := by
      simp only [lenx, Nat.sub_one_add_one <| JH_pos_len JHx,
        JHx.filtration_length] at hlast_step
      exact ((hsl.seesaw_total_eq_right_iff hx0_bot nt).2 hlast_step).symm
    let : FiniteTotalPayoff (Resμ Ires μ) :=
      { fin_tot_payoff := by simpa only [Resμ] using hstepx0.symm ▸ hftp.fin_tot_payoff }
    let JH_raw : ℕ → ↥Ires := fun n ↦ ⟨x0 ⊔ JHy.filtration n, ⟨le_sup_left, le_top⟩⟩
    have JH_raw_antitone : Antitone JH_raw :=
      fun _ _ hn ↦ sup_le_sup_left (JHy.antitone hn) _
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simpa only [JH_raw, JHy.first_eq_top, le_top, sup_of_le_right, JH_raw] using by rfl
    have hJHy_last : JHy.filtration leny = ⊥ := JHy.filtration_length
    have JH_raw_fin_len : JH_raw leny = ⊥ := by
      simpa only [JH_raw, leny, hJHy_last, bot_le, sup_of_le_left, JH_raw] using by rfl
    let atRaw : ∃ k, JH_raw k = ⊥ := ⟨leny, JH_raw_fin_len⟩
    let JHfinal := fun n ↦ JH_raw (subseqIdx JH_raw atRaw JH_raw_antitone n)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simpa [JHfinal, subseqIdx] using JH_raw_first_top
    have hμmax : μmax μ ⊤ = μ ⊤ :=
      PayoffFunction.max_top_eq_apply_iff.2
        (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
    have hμA_eq_tot : ∀ (JH : JordanHolderFiltration μ) (k : ℕ), (hk : k < JH.length) →
      μ ⊤ = μA μ ⟨⊥, JH.filtration k,
        JH.filtration_length ▸ JH.strict_anti hk.le (le_rfl : JH.length ≤ _) hk⟩ := by
      intro JH k hk
      rw [← μA_eq_μmin μ]
      have hess := μ_bot_JH_eq_μ_tot JH k hk
      rw [← hess]
      refine eq_of_le_of_ge ?_ ?_
      · refine le_iInf₂ fun u hu1 ↦ ?_
        if hubot : u = ⊥ then simp only [hubot, le_refl]
        else
          by_contra! hc
          replace hc := (hsl.seesaw_right_lt_total_iff
            (bot_lt_iff_ne_bot.2 hubot) hu1.2).1 hc
          rw [hess] at hc
          have hμu : μ ⟨⊥, u, bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μ ⊤ := by
            rw [← hμmax]
            exact le_iSup₂_of_le u ⟨bot_lt_iff_ne_bot.2 hubot, le_top⟩ le_rfl
          exact not_le_of_gt hc hμu
      · exact PayoffFunction.min_le_apply
    have hcond1 : ∀ i < Nat.find atRaw, ∀ hfi : JH_raw (i + 1) < JH_raw i,
      (fun z ↦ Resμ Ires μ z = Resμ Ires μ ⊤)
              ⟨JH_raw (i + 1), JH_raw i, hfi⟩ := by
      intro j hj hfj
      simp only [Resμ, PayoffFunction.coe_mk, StrictIntvl.ofSub, JH_raw]
      have hj' : ∀ j : ℕ, j ≤ leny → μ ⟨⊥, x0 ⊔ JHy.filtration j, lt_of_lt_of_le hx0_bot
        le_sup_left⟩ = μ ⊤ := by
        refine fun j hj ↦ eq_of_le_of_ge ?_ ?_
        · rw [← hμmax]
          exact le_iSup₂_of_le (x0 ⊔ JHy.filtration j)
            ⟨lt_of_lt_of_le hx0_bot le_sup_left, le_top⟩ le_rfl
        · refine le_trans ?_ (PayoffFunction.min_le_apply (μ := μ)
            (I := ⟨⊥, x0 ⊔ JHy.filtration j, lt_of_lt_of_le hx0_bot le_sup_left⟩))
          change μ ⊤ ≤ μmin μ ⟨⊥, x0 ⊔ JHy.filtration j, lt_of_lt_of_le hx0_bot le_sup_left⟩
          rw [μA_eq_μmin μ ⟨⊥, x0 ⊔ JHy.filtration j,
            lt_of_lt_of_le hx0_bot le_sup_left⟩]
          if hjbot : ⊥ = JHy.filtration j  then
            simp only [← hjbot, bot_le, sup_of_le_left]
            rw [← μA_eq_μmin μ, ← JHx.step_cond₁ (lenx - 1) (Nat.sub_one_lt (JH_pos_len JHx))]
            refine le_iInf₂ fun u hu1 ↦ ?_
            replace := JHx.step_cond₂ (lenx - 1) (Nat.sub_one_lt (JH_pos_len JHx)) u
            simp only [lenx, Nat.sub_one_add_one <| JH_pos_len JHx, JHx.filtration_length] at *
            if ubot : u = ⊥ then simpa only [ubot] using le_rfl
            else
              replace := this (bot_lt_iff_ne_bot.2 ubot) hu1.2
              exact le_of_lt <| (hsl.seesaw_total_lt_right_iff
                (bot_lt_iff_ne_bot.2 ubot) hu1.2).2 this
          else
          replace : μA μ ⟨⊥, x0, hx0_bot⟩ ⊓ μA μ ⟨⊥, JHy.filtration j, Ne.bot_lt' hjbot⟩ ≤
              μA μ ⟨⊥, x0 ⊔ JHy.filtration j, lt_sup_of_lt_left hx0_bot⟩ :=
            (inferInstance : μ.IsConvexOn ⊤).inf_A_le_A_sup (StrictIntvl.mem_top _)
              (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hx0_bot (Ne.bot_lt' hjbot)
          convert this
          have t2 := hμA_eq_tot JHy j <| by
            refine lt_of_le_of_ne hj ?_
            by_contra hc
            exact hjbot (hc ▸ JHy.filtration_length).symm
          rw [← (hμA_eq_tot JHx (lenx - 1) (by omega)), ← t2]
          exact Eq.symm (min_self (μ ⊤))
      have tj1 := hj' j (le_of_lt <| lt_of_lt_of_le hj <| Nat.find_min' atRaw JH_raw_fin_len)
      have := tj1 ▸ ((hsl.seesaw_total_eq_right_iff
        (lt_of_lt_of_le hx0_bot le_sup_left) hfj).2 <|
        tj1 ▸ hj' (j + 1) (lt_of_lt_of_le hj <| Nat.find_min' atRaw JH_raw_fin_len))
      rw [← this]
      exact hstepx0.symm
    let JH_FINAL : JordanHolderFiltration (Resμ Ires μ) := by
      refine JordanHolderFiltration.mk JHfinal (by
        intro i j hij
        change JH_raw (subseqIdx JH_raw atRaw JH_raw_antitone j) ≤
          JH_raw (subseqIdx JH_raw atRaw JH_raw_antitone i)
        exact JH_raw_antitone <|
          (strictMono_nat_of_lt_succ (subseqIdx.lt_succ JH_raw atRaw JH_raw_antitone)).monotone hij)
        (subseqIdx_hits_bot JH_raw atRaw JH_raw_antitone JH_raw_first_top)
        (fun i _ j hj hij ↦
          subseqIdx_strictAnti JH_raw JH_raw_first_top atRaw JH_raw_antitone i j hij hj)
        JHfinal_first_top
        (subseqIdx_inherit_step_predicate JH_raw JH_raw_first_top atRaw JH_raw_antitone
          (fun z ↦ (Resμ Ires μ) z = (Resμ Ires μ) ⊤) hcond1) ?_
      · refine fun i hi ↦
          subseqIdx_inherit_step_predicate JH_raw JH_raw_first_top atRaw JH_raw_antitone
          (fun w ↦ ∀ z : ↥Ires, (hw : w.left < z) → z < w.right →
            (Resμ Ires μ) ⟨w.left, z, hw⟩ < (Resμ Ires μ) w)
          (fun j hj hfj w hw1 hw2 ↦ (hsl.seesaw_total_lt_right_iff
              (x := ↑(JH_raw (j + 1))) (y := ↑w) (z := ↑(JH_raw j)) hw1 hw2).1 ?_) i hi
        have := hcond1 j hj hfj
        simp only [Resμ, PayoffFunction.coe_mk, StrictIntvl.ofSub] at this
        have this' := JHx.step_cond₁ (JHx.length - 1) (Nat.sub_one_lt (JH_pos_len JHx))
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx, JHx.filtration_length] at this'
        replace this' := (hsl.seesaw_total_eq_right_iff hx0_bot nt).2 this'
        rw [this]
        have hproblem : JHy.filtration (j + 1) ≠ JHy.filtration j ⊓ ↑w := by
          by_contra hc
          simp only [JH_raw] at hw1
          simp only [JH_raw] at hw2
          have := @hmod.sup_inf_le_assoc_of_le x0 (JHy.filtration j) w.val
            (le_of_lt <| lt_of_le_of_lt le_sup_left hw1)
          rw [← hc, inf_eq_right.2 <|
            (le_of_lt hw2 : (↑w : ℒ) ≤ x0 ⊔ JHy.filtration j)] at this
          exact (not_le_of_gt hw1) this
        have hnle : ¬ (JHy.filtration j ≤ w) := by
          by_contra hc
          simp only [JH_raw] at hw2
          refine (not_le_of_gt hw2) <| sup_le_iff.2 ⟨?_,hc⟩
          simp only [JH_raw] at hw1
          apply le_of_lt <| lt_of_le_of_lt le_sup_left hw1
        have heqs : μ ⟨↑w, ↑(JH_raw j), hw2⟩ =
          μ ⟨JHy.filtration j ⊓ w, JHy.filtration j,inf_lt_left.2 hnle⟩ := by
          rw [affine.eq (JHy.filtration j) w.val hnle]
          have : ↑(JH_raw j) = JHy.filtration j ⊔ w.val := by
            simp only [JH_raw]
            apply eq_of_le_of_ge ?_ ?_
            · simp only [JH_raw] at hw1
              replace hw1 := sup_le_sup_right
                (le_of_lt hw1 : x0 ⊔ JHy.filtration (j + 1) ≤ ↑w) (JHy.filtration j)
              replace := left_eq_sup.2 <| JHy.antitone (Nat.le_add_right j 1)
              rw [sup_comm] at this
              rw [sup_assoc, ← this] at hw1
              nth_rw 2 [sup_comm] at hw1
              exact hw1
            · simp only [JH_raw] at hw2
              replace hw2 := sup_le_sup_right
                (le_of_lt hw2 : (↑w : ℒ) ≤ x0 ⊔ JHy.filtration j) (JHy.filtration j)
              nth_rw 1 [sup_assoc,sup_comm] at hw2
              simp only [forall_exists_index, Nat.lt_find_iff, ne_eq,
                le_refl, sup_of_le_left, sup_le_iff, le_sup_right, true_and, ge_iff_le, JH_raw] at *
              exact hw2
          simp only [this]
        simp only [StrictIntvl.left_top, StrictIntvl.right_top]
        rw [heqs, ((by rfl) : μ ⟨↑(⊥ : ↥Ires), ↑(⊤ : ↥Ires), nt⟩ =
          μ ⟨x0, ⊤, nt⟩), ← this', StrictIntvl.mk_bot_top, ← JHy.step_cond₁ j <|
          lt_of_lt_of_le hj <| Nat.find_le JH_raw_fin_len]
        have hlt : JHy.filtration (j+1) < JHy.filtration j ⊓ w := by
          refine lt_of_le_of_ne (le_inf (JHy.antitone <| Nat.le_add_right j 1) ?_) hproblem
          simp only [sup_comm, JH_raw] at hw1
          exact le_of_lt <| lt_of_le_of_lt (le_sup_left) hw1
        refine (hsl.seesaw_total_lt_right_iff hlt (inf_lt_left.2 hnle)).2 ?_
        exact JHy.step_cond₂ j (by
          replace this' := Nat.find_min atRaw hj
          unfold JH_raw at this'
          by_contra hcontra
          push Not at hcontra
          replace : JHy.filtration j = ⊥ :=
            le_bot_iff.mp <| (JHy.filtration_length) ▸ JHy.antitone hcontra
          rw [this] at this'
          simp only [bot_le, sup_of_le_left] at this'
          exact this' rfl
          ) (JHy.filtration j ⊓ w) hlt <| inf_lt_left.mpr hnle
    have ha : JH_FINAL.length < leny := by
      have : JHfinal leny = ⊥ := by
        simp only [JHfinal]
        exact eq_bot_iff.2 <| JH_raw_fin_len ▸
          JH_raw_antitone (subseqIdx.ge_self JH_raw atRaw JH_raw_antitone leny)
      refine lt_of_le_of_ne (JH_FINAL.length_le_of_eq_bot this) ?_
      · let i0 := Nat.findGreatest (fun n ↦ JHx.filtration (JHx.length -1) ≤
          JHy.filtration n) (leny - 1)
        refine subseqIdx_find_ne_of_plateau
          JH_raw JH_raw_first_top atRaw JH_raw_antitone leny JH_raw_fin_len
          ⟨i0,⟨Nat.add_le_of_le_sub (Nat.one_le_iff_ne_zero.mpr <| JH_pos_len JHy) <|
            Nat.findGreatest_le (leny - 1),?_⟩⟩
        · replace := @Nat.findGreatest_spec 0 (fun n ↦ x0 ≤ JHy.filtration n)
            inferInstance (leny - 1) (Nat.zero_le _) (by simp only [JHy.first_eq_top, le_top])
          have hi0_last : ¬ i0 + 1 ≤ leny - 1 → i0 + 1 = leny := by
            intro hw
            refine le_antisymm ?_ <| le_of_not_gt fun hlt ↦ hw <|
              (Nat.le_sub_one_iff_lt <| zero_lt_iff.2 <| JH_pos_len JHy).2 hlt
            exact Nat.add_le_of_le_sub
              (Nat.one_le_iff_ne_zero.mpr <| JH_pos_len JHy) <| Nat.findGreatest_le (leny - 1)
          have hi0_imp : ¬ x0 ≤ JHy.filtration (i0 + 1) := by
            by_cases hw : i0 + 1 ≤ leny - 1
            · exact Nat.findGreatest_is_greatest (lt_add_one _) hw
            · simp only [hi0_last hw, leny, JHy.filtration_length, le_bot_iff]
              exact JHx.ne_bot_of_lt_length (Nat.sub_one_lt <| JH_pos_len JHx)
          have h1 : JH_raw (i0 + 1) = JHy.filtration i0 := by
            refine eq_of_le_of_not_lt (sup_le this <| JHy.antitone (Nat.le_add_right i0 1))
              <| fun hc ↦ ?_
            replace : i0 ≤ leny - 1 := Nat.findGreatest_le (leny - 1)
            have hsmall : JHy.filtration (i0 + 1) < ↑(JH_raw (i0 + 1)) := by
              refine lt_of_le_of_ne le_sup_right ?_
              · by_contra hcon
                if hw : i0 + 1 ≤ leny - 1 then
                  exact @Nat.findGreatest_is_greatest (i0+1) (fun n ↦ x0 ≤ JHy.filtration n)
                    inferInstance (leny - 1) (lt_add_one _) hw <| right_eq_sup.1 hcon
                else exact hi0_imp <| right_eq_sup.1 hcon
            have otherwise := JHy.step_cond₂ i0 ((Nat.le_sub_one_iff_lt <| zero_lt_iff.2 <|
              JH_pos_len JHy).1 this) ↑(JH_raw (i0 + 1)) hsmall hc
            rw [JHy.step_cond₁ i0 <| lt_of_le_of_lt this <| Nat.sub_one_lt <| JH_pos_len JHy ]
              at otherwise
            refine (lt_iff_not_ge.1 otherwise) ?_
            rw [← JHx.step_cond₁ (JHx.length - 1) (Nat.sub_one_lt (JH_pos_len JHx))]
            rw [(affine.eq x0 (JHy.filtration (i0 + 1)) hi0_imp).symm]
            if hif : JHx.filtration (JHx.length) =
              JHx.filtration (JHx.length - 1) ⊓ JHy.filtration (i0 + 1) then
              apply le_of_eq
              simp [lenx, x0, Nat.sub_one_add_one <| JH_pos_len JHx, hif]
            else
              have hh : JHx.filtration (JHx.length) <
                JHx.filtration (JHx.length - 1) ⊓ JHy.filtration (i0 + 1) := by
                simp only [JHx.filtration_length] at hif
                simpa [JHx.filtration_length] using Ne.bot_lt' hif
              replace := le_of_lt <| JHx.step_cond₂ (JHx.length - 1)
                (Nat.sub_one_lt <| JH_pos_len JHx)
                (JHx.filtration (JHx.length - 1) ⊓ JHy.filtration (i0 + 1))
                ((Nat.sub_one_add_one <| JH_pos_len JHx) ▸ hh) <| inf_lt_left.mpr hi0_imp
              simp only [Nat.sub_one_add_one <| JH_pos_len JHx] at this
              exact byContradiction fun hcc ↦ (lt_iff_not_ge.1 <|
                (hsl.seesaw_right_lt_total_iff hh (inf_lt_left.mpr hi0_imp)).1 <|
                  lt_of_not_ge (by
                    simpa only [Nat.sub_one_add_one <| JH_pos_len JHx] using hcc)) this
          exact Subtype.coe_inj.1 <| h1 ▸ (sup_eq_right.2 this)
    let JHfun : ℕ → ↥Ires := fun n ↦
      if hn : n ≤ JHx.length - 1 then ⟨JHx.filtration n,⟨JHx.antitone hn,le_top⟩⟩
      else ⊥
    have JHfun_fin_len : ∃ N : ℕ, JHfun N = ⊥ := by
      simp only [JHfun]
      use JHx.length
      simp only [lt_iff_not_ge.1 <| Nat.sub_one_lt <| JH_pos_len JHx, ↓reduceDIte]
    have JHfun_antitone : Antitone JHfun := by
        intro n1 n2 hn
        by_cases h3 : n2 ≤ JHx.length - 1
        · simp only [JHfun, le_trans hn h3, h3, ↓reduceDIte]
          exact JHx.antitone hn
        · simp only [h3, ↓reduceDIte, bot_le, JHfun]
    have hhard : Nat.find JHfun_fin_len = JHx.length - 1 := by
      have hgreat : Nat.find JHfun_fin_len ≤ JHx.length - 1 := by
        refine Nat.find_min' JHfun_fin_len ?_
        simpa only [JHfun, le_refl, ↓reduceDIte] using by rfl
      refine eq_of_le_of_not_lt hgreat fun hv ↦ ?_
      have hweired : JHx.filtration (Nat.find JHfun_fin_len) =
        JHx.filtration (JHx.length - 1) := by
        have this' := Nat.find_spec JHfun_fin_len
        simp only [JHfun, hgreat, ↓reduceDIte] at this'
        exact Subtype.coe_inj.2 this'
      have hlt : JHx.filtration (JHx.length - 1) < JHx.filtration (Nat.find JHfun_fin_len) :=
        JHx.strict_anti (Set.mem_Iic.mpr (hv.le.trans (Nat.sub_le (JHx.length) 1)))
          (Set.mem_Iic.mpr (Nat.sub_le (JHx.length) 1)) hv
      exact (lt_self_iff_false (JHx.filtration (JHx.length - 1))).1 (hweired ▸ hlt)
    let JHres : JordanHolderFiltration (Resμ Ires μ) := by
      refine JordanHolderFiltration.mk
        JHfun JHfun_antitone JHfun_fin_len (fun i _ j hj hij ↦ ?_) ?_ ?_ ?_
      · rw [Set.mem_Iic] at hj
        simp only [JHfun,hhard ▸ hj,le_of_lt <| lt_of_lt_of_le hij (hhard ▸ hj),↓reduceDIte]
        have := JHx.strict_anti (hij.le.trans (le_trans (hhard ▸ hj) <|
            le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx))
          (le_trans (hhard ▸ hj) <| le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx) hij
        exact Subtype.coe_lt_coe.1 this
      · simpa only [JHfun, zero_le, ↓reduceDIte, JHx.first_eq_top] using by rfl
      · intro k1 hk1
        simp only [Resμ, JHfun]
        replace hk1 := hhard ▸ hk1
        have hk1' : k1 + 1 ≤ JHx.length - 1 := hk1
        simp only [le_of_lt hk1, ↓reduceDIte, hk1']
        exact (JHx.step_cond₁ k1 <| Nat.lt_of_lt_pred hk1).trans hstepx0.symm
      · intro i hi z hz hz'
        simp only [Resμ]
        have hi' : i + 1 ≤ JHx.length - 1 := hhard ▸ hi
        have htemp : JHx.filtration (i + 1) < z.val := by
          simp only [JHfun, hi', ↓reduceDIte] at hz
          exact hz
        have htemp2 : z < JHx.filtration i := by
          simp only [JHfun, le_of_lt <| hhard ▸ hi, ↓reduceDIte] at hz'
          exact hz'
        simp only [JHfun]
        simp only [hi', ↓reduceDIte, le_of_lt <| hhard ▸ hi, gt_iff_lt]
        exact JHx.step_cond₂ i (Nat.lt_of_lt_pred <| hhard ▸ hi) z htemp htemp2
    let : PayoffFunction.IsSemistable (Resμ Ires μ) := semistable_resμ_of_jordanHolderFiltration _ _
    exact Nat.le_add_of_sub_le <| hhard ▸ hn (μ := Resμ Ires μ)
      ⟨JH_FINAL, Nat.le_of_lt_succ <| Nat.lt_of_lt_of_le ha hJHy⟩ JHres


end impl

end HarderNarasimhan
