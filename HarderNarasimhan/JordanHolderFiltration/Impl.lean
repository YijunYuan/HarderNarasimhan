/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl
import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
import HarderNarasimhan.JordanHolderFiltration.Defs
import HarderNarasimhan.SlopeLike.Result
import HarderNarasimhan.FirstMoverAdvantage.Results
import HarderNarasimhan.Convexity.Results
import Mathlib.Data.Finite.Card
import Mathlib.Order.ModularLattice

/-!
  # Jordan–Hölder filtrations: internal implementation

  This file implements the construction and main internal properties of Jordan–Hölder
  filtrations.

  The core object is the recursively defined chain `JHFil μ ... : ℕ → ℒ`, built by
  repeatedly choosing a minimal element in a suitable set of candidates with constant
  total payoff. The lemmas `JHFil_prop₁` and `JHFil_prop₂` establish the defining step
  conditions of a `JordanHolderFiltration`.

  The middle part of the file develops a generic subsequence construction (`subseq`) for
  turning a chain that eventually hits `⊥` into a normalised chain starting at `⊤` and
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
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥, ⊤), bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) →
  ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc n ∧ μ ⟨(⊥,p),h⟩ =
      μ ⟨(⊥,⊤),bot_lt_top⟩}
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
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥, ⊤), bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ, JHFil μ hμ hμsl hst hdc k > ⊥ →
  JHFil μ hμ hμsl hst hdc k > JHFil μ hμ hμsl hst hdc (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ =
    μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simpa only [h]

open Classical in
/-- `JHFil_prop₁` proves the first step condition for the chain `JHFil`.

  For each index `k` with `JHFil ... k > ⊥`, the payoff of the step
  `(JHFil ... (k+1), JHFil ... k)` is equal to the total payoff `μ (⊥, ⊤)`.
-/
lemma JHFil_prop₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥, ⊤), bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N + 1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1),
  JHFil μ hμ hμsl hst hdc k),JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk'
    simp only [JHFil]
    by_cases this : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · simp only [this]
      have this' := (hacc.wf.has_min _ this).choose_spec.1.2.2
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _
        this).choose ⊤ ⟨(hacc.wf.has_min _ this).choose_spec.1.choose,(hacc.wf.has_min _ this
        ).choose_spec.1.out.choose_spec.1⟩) (by aesop)) (by aesop)).2.symm
    · simp only [this, ↓reduceDIte]
  | succ k hk =>
    intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ =
      μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this, Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt,
        lt_self_iff_false] at hk'
    have jh_kp1_ntop' : JHFil μ hμ hμsl hst hdc k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil,jh_kp1_ntop]
      exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
    have bot_jh_kp1_eq_ans := (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.2.2
    by_cases jh_kp2_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc (k + 1) ∧ μ ⟨(⊥,p),h⟩
      = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · have smart : μ ⟨(⊥, (hacc.wf.has_min _ jh_kp2_ntop).choose), (hacc.wf.has_min _ jh_kp2_ntop
        ).choose_spec.1.out.1⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ := by
        rw [(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.2,← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop ]
        simp only [exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
          ↓reduceDIte]
      have hfinal : μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ =
        μ ⟨((hacc.wf.has_min _ jh_kp2_ntop).choose, JHFil μ hμ hμsl hst hdc (k + 1)),
        (hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.1⟩ := by
        refine (Or.resolve_left ((Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥
          (hacc.wf.has_min _ jh_kp2_ntop).choose (JHFil μ hμ hμsl hst hdc (k + 1))
          ⟨(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose,(hacc.wf.has_min _ jh_kp2_ntop
          ).choose_spec.1.out.choose_spec.1⟩) (?_)) (?_)).2
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]; simp only [JHFil,jh_kp1_ntop]
          simp only [↓reduceDIte,
            exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
            lt_self_iff_false, not_false_eq_true]
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]; simp only [JHFil,jh_kp1_ntop]
          simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
            forall_exists_index, lt_self_iff_false, not_false_eq_true]
      conv_lhs =>
        arg 1; arg 1; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
          forall_exists_index]
      simp only [exists_and_left, Set.mem_setOf_eq, and_imp,
        forall_exists_index] at hfinal
      rw [← hfinal]
      simp only [JHFil,jh_kp1_ntop]
      simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, and_imp,
        forall_exists_index]
      simp only [exists_and_left, Set.mem_setOf_eq, and_imp,
        forall_exists_index] at bot_jh_kp1_eq_ans
      exact bot_jh_kp1_eq_ans
    · conv_lhs =>
        arg 1; arg 1; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp only [↓reduceDIte]
      have this': μ ⟨(⊥, JHFil μ hμ hμsl hst hdc k), jh_kp1_ntop'⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        by_cases hh : k = 0
        · simp only [hh,JHFil]
        · have : JHFil μ hμ hμsl hst hdc k = JHFil μ hμ hμsl hst hdc ((k-1)+1) := by
            simp only [Nat.sub_one_add_one hh]
          simp only [this]
          have : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k-1) ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤),
            bot_lt_top⟩}.Nonempty := by
            by_contra hthis
            rw [this] at jh_kp1_ntop'
            simp only [JHFil,hthis] at jh_kp1_ntop'; simp only [↓reduceDIte, gt_iff_lt,
              lt_self_iff_false] at jh_kp1_ntop'
          simp only [JHFil,this]
          simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, and_imp,
            forall_exists_index]
          simpa only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
            forall_exists_index] using (hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.2
      simp only [← this']
      have : JHFil μ hμ hμsl hst hdc (k + 1) < JHFil μ hμ hμsl hst hdc k := by
        simpa only [JHFil,jh_kp1_ntop] using (hacc.wf.has_min _ jh_kp1_ntop
          ).choose_spec.1.out.choose_spec.1
      have this'' :  μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ = μ ⟨(JHFil μ hμ hμsl hst hdc
        (k + 1), JHFil μ hμ hμsl hst hdc k), this⟩ := by
        rw [hk jh_kp1_ntop',← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, and_imp,
          forall_exists_index]
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst
        hdc (k + 1)) (JHFil μ hμ hμsl hst hdc k) ⟨hk',this⟩) (fun this_1 ↦ ne_of_lt
        (lt_trans this_1.left this_1.right) this'')) (fun this_1 ↦ ne_of_lt
        (gt_trans this_1.1 this_1.2) (Eq.symm this''))).1



/-- `JHFil_fin_len` shows that the chain `JHFil` reaches `⊥` after finitely many steps.

  The proof uses the strengthened descending-chain condition `hdc` applied to the chain
  itself: if `⊥` were never reached, `hdc` would force a step payoff to be `⊤`, contradicting
  the finite-total-payoff assumption together with `JHFil_prop₁`.
-/
lemma JHFil_fin_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥, ⊤), bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∃ N : ℕ, JHFil μ hμ hμsl hst hdc N = ⊥ := by
  by_contra hc
  simp only [not_exists] at hc
  rcases hdc (fun n => JHFil μ hμ hμsl hst hdc n) <| strictAnti_of_add_one_lt <|
    fun n _ ↦ JHFil_anti_mono μ hμ hμsl hst hdc n (bot_lt_iff_ne_bot.2 <| hc n) with ⟨N, hN⟩
  exact hμ.symm <| hN ▸ JHFil_prop₁ μ hμ hμsl hst hdc N (bot_lt_iff_ne_bot.2 <| hc N)

open Classical in
/-- `JHFil_prop₂` proves the stability step condition for the chain `JHFil`.

  For each `k` with `JHFil ... k > ⊥` and any strict intermediate `z` between
  `JHFil ... (k+1)` and `JHFil ... k`, the payoff strictly decreases when refining the step
  through `z`.
-/
lemma JHFil_prop₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [hwdcc' : StrongDescendingChainCondition' μ]
(hμ : μ ⟨(⊥, ⊤), bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → ∀ z : ℒ, (h' : JHFil μ hμ hμsl hst hdc (k + 1) < z)
  → (h'' : z < JHFil μ hμ hμsl hst hdc k) →
  μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), z), h'⟩ < μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1),
    JHFil μ hμ hμsl hst hdc k), JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ := by
  intro k hk z h' h''
  have this_new : Semistable μ → μmax μ TotIntvl = μ TotIntvl :=
    fun a ↦ (List.TFAE.out (impl.thm4d21 μ hμsl inferInstance inferInstance).1 0 3).2
      ((impl.thm4d21 μ hμsl inferInstance inferInstance).2.1 a)
  specialize this_new hst
  simp only [μmax, TotIntvl, ne_eq] at this_new
  have this_q: μ ⟨(⊥, z), lt_of_le_of_lt bot_le h'⟩ ≤ μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    rw [← this_new]
    apply le_sSup
    use z, ⟨in_TotIntvl z, Ne.symm <| bot_lt_iff_ne_bot.1 <| lt_of_le_of_lt bot_le h'⟩
  by_cases hfp1bot : JHFil μ hμ hμsl hst hdc (k + 1) = ⊥
  · simp only [hfp1bot]
    have : ¬ {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ =
      μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this] at hfp1bot
      have := (hacc.wf.has_min _ this).choose_spec.1.out.choose
      simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, and_imp,
        forall_exists_index] at hfp1bot
      simp only [exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index] at this
      exact (ne_of_lt this) hfp1bot.symm
    apply Set.not_nonempty_iff_eq_empty.1 at this
    apply Set.eq_empty_iff_forall_notMem.1 at this
    specialize this z
    simp only [exists_and_left, Set.mem_setOf_eq, not_and, not_exists] at this
    replace := lt_of_le_of_ne this_q <| this h'' (lt_of_le_of_lt bot_le h')
    by_cases hk' : k = 0
    · simpa only [hk',JHFil]
    · conv_rhs =>
        arg 1; arg 1; arg 2; arg 6
        rw [← Nat.sub_one_add_one hk']
      have hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k - 1) ∧ μ ⟨(⊥, p), h⟩ =
        μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
        by_contra!
        have this': JHFil μ hμ hμsl hst hdc k = JHFil μ hμ hμsl hst hdc ((k-1)+1) := by
          conv_lhs =>
            arg 6
            rw [← Nat.sub_one_add_one hk']
        simp only [this',JHFil,this] at hk
        simp only [Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt, lt_self_iff_false] at hk
      rw [← (hacc.wf.has_min _ hne).choose_spec.1.out.2.2] at this
      simp only [JHFil,hne]
      simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
        forall_exists_index]
      simpa only [exists_and_left, Set.mem_setOf_eq,
        gt_iff_lt, and_imp, forall_exists_index] using this
  · have h''' : μ ⟨(⊥, z), lt_of_le_of_lt bot_le h'⟩ < μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
      refine lt_of_le_of_ne this_q ?_
      by_contra!
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧
        μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · have := (hacc.wf.has_min _ hne).choose_spec.2 z (by use lt_of_le_of_lt bot_le h')
        simp only [JHFil,hne] at h'
        simp only [gt_iff_lt, exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this h'
      · refine hne ?_
        use z, lt_of_le_of_lt bot_le h'
    have h'''' : μ ⟨(⊥, ⊤), bot_lt_top⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)),
      bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ =
        μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · simp only [JHFil,hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp only [gt_iff_lt, exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this.symm
      · simp only [JHFil,hne] at hfp1bot
        simp only [↓reduceDIte, not_true_eq_false] at hfp1bot
    exact (JHFil_prop₁ μ hμ hμsl hst hdc k hk ).symm ▸ lt_trans ((Or.resolve_right <|
      (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst hdc (k + 1)) z
      ⟨bot_lt_iff_ne_bot.2 hfp1bot,h'⟩) (not_and_iff_not_or_not.2 <| Or.inl <| not_lt_of_gt <|
      h'''' ▸ h''')) (not_and_iff_not_or_not.2 <| Or.inl <| ne_of_gt <| h'''' ▸ h''')).2 h'''

open Classical in
/-- `JH_pos_len` is a small normalisation lemma: any Jordan–Hölder filtration has
  positive length (i.e. its `fin_len` witness cannot be `0`) because the filtration starts
  at `⊤`.
-/
lemma JH_pos_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} : ∀ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≠ 0 := by
  intro JH h
  simp only [Nat.find_eq_zero, JH.first_eq_top, top_ne_bot] at h

open Classical in
/-- `subseq f atf` is a normalised subsequence extracted from a chain `f : ℕ → ℒ` that
  eventually hits `⊥`.

  The construction starts at `⊤`, then repeatedly jumps forward to the first index where
  `f` falls strictly below the previous value; once `⊥` is reached, it stays constant.
-/
noncomputable def subseq {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : ℕ → ℒ := fun n ↦
  match n with
  | 0 => ⊤
  | t + 1 =>
    if hcond : subseq f atf t = ⊥ then
      ⊥
    else
      f <| Nat.find (⟨atf.choose,atf.choose_spec.symm ▸ bot_lt_iff_ne_bot.2 hcond⟩ :
        ∃ k : ℕ, f k < subseq f atf t)

/-- `subseq.pf2` packages the witness that, as long as `subseq f atf t ≠ ⊥`, there exists an
  index where `f` is strictly below the current subsequence value.
  This is used to justify the `Nat.find` step in the definition of `subseq`.
-/
private lemma subseq.pf2 {ℒ : Type u_1} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ)
  (atf : ∃ k, f k = ⊥) (t : ℕ) (hcond : ¬subseq f atf t = ⊥) : ∃ k, f k < subseq f atf t :=
  ⟨atf.choose,atf.choose_spec.symm ▸ bot_lt_iff_ne_bot.2 hcond⟩

open Classical in
/-- `subseq_prop0` states that every value of the original chain `f` appears somewhere in
  the extracted subsequence.

  This is the basic surjectivity property needed to compare the two chains.
-/
lemma subseq_prop0 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (hf0 : f 0 = ⊤) :
  ∀ i : ℕ, ∃ j : ℕ, f i = subseq f atf j := by
  intro i
  induction i with
  | zero => exact ⟨0,hf0⟩
  | succ i hi =>
    rcases hi with ⟨j,hj⟩
    if h : f i = ⊥ then
      use j
      rw [← hj,h]
      exact le_bot_iff.1 <| h ▸ hf (Nat.le_succ i)
    else
    if h' : f i = f (i+1) then
      exact ⟨j,h' ▸ hj⟩
    else
      use j+1
      simp only [subseq,hj ▸ h, ↓reduceDIte]
      have hq := subseq.pf2 f atf j (Eq.mpr_not (eq_false (hj ▸ h))
        (of_eq_false (Eq.refl False)))
      have : i + 1 = Nat.find hq := by
        apply eq_of_le_of_ge
        · have : Nat.find hq > i := by
            by_contra hu
            apply le_of_not_gt at hu
            have hg := hj ▸ lt_of_le_of_lt (hf hu) (Nat.find_spec hq)
            exact (lt_self_iff_false (subseq f atf j)).mp hg
          exact this
        · by_contra!
          exact (hj ▸ Nat.find_min hq this) <| lt_of_le_of_ne (hf <| Nat.le_succ i) <| Ne.symm h'
      exact congrArg f this

open Classical in
/-- `subseq_prop0'` is a monotone-index refinement of `subseq_prop0`.

  It produces an index `j ≥ i` such that `subseq f atf i = f j`.
-/
lemma subseq_prop0' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (hf0 : f 0 = ⊤) :
∀ i : ℕ, ∃ j : ℕ, j ≥ i ∧ subseq f atf i = f j:= by
  intro i
  induction i with
  | zero =>
    use 0
    simp only [subseq, ge_iff_le, le_refl, and_self, hf0]
  | succ i hi =>
    simp only [subseq]
    if hcond : subseq f atf i = ⊥ then
      simp only [ge_iff_le, hcond, ↓reduceDIte]
      rcases hi with ⟨t,ht⟩
      rw [hcond] at ht
      use t + 1
      simp only [add_le_add_iff_right, true_and, ht]
      exact ht.2 ▸ (Eq.symm <| le_bot_iff.1 <| ht.2 ▸ hf (Nat.le_succ t))
    else
    simp only [ge_iff_le, hcond, ↓reduceDIte]
    have hq := subseq.pf2 f atf i (of_eq_false (eq_false hcond))
    rcases hi with ⟨t,ht⟩
    rw [ht.2] at hq
    use Nat.find hq
    constructor
    · have : Nat.find hq > t := by
        by_contra d
        apply le_of_not_gt at d
        if hy: Nat.find hq = t then
          exact (lt_self_iff_false (f t)).mp (Eq.mp (congrArg (fun _a ↦ f _a < f t) hy) <|
            Nat.find_spec hq)
        else
        exact (lt_self_iff_false (f <| Nat.find hq)).1 <| lt_of_lt_of_le (Nat.find_spec hq) <|
          hf <| le_of_lt <| lt_of_le_of_ne d hy
      linarith
    simp only [ht]

/-- `subseq_prop1` shows that the normalised subsequence `subseq f atf` eventually reaches `⊥`.

  Concretely, it produces an index `N` with `subseq f atf N = ⊥`, using the witness from `atf` and
  the basic property `subseq_prop0`.
-/
lemma subseq_prop1 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ)
  (atf : ∃ k, f k = ⊥) (hf : Antitone f) (hf0 : f 0 = ⊤) : ∃ N : ℕ, subseq f atf N = ⊥ := by
  rcases (subseq_prop0 f atf hf hf0 atf.choose) with ⟨N,hN⟩
  exact ⟨N, hN ▸ atf.choose_spec⟩

open Classical in
/-- `subseq_prop2` records that the subsequence construction preserves antitonicity.

  Even though indices are changed by a greedy choice, the values `subseq f atf i` form an antitone
  chain in `ℒ`.
-/
lemma subseq_prop2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ)
  (atf : ∃ k, f k = ⊥) : Antitone (subseq f atf) := by
  intro i j
  apply Nat.le_induction
  · exact le_rfl
  · refine fun n hn hn' ↦ le_trans ?_ hn'
    if hnzero : n = 0 then
      exact hnzero ▸ le_top
    else
    simp only [subseq]
    if hcond : subseq f atf n = ⊥ then
      simp only [hcond, ↓reduceDIte, le_refl]
    else
    simpa only [hcond, ↓reduceDIte] using le_of_lt <| Nat.find_spec <|
      subseq.pf2 f atf n (of_eq_false (eq_false hcond))


/-- `subseq_prop3` compares the subsequence with the original chain pointwise.

  It proves `subseq f atf k ≤ f k` for all `k`, i.e. the normalised chain does not sit above the
  original chain at the same index.
-/
lemma subseq_prop3 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f) :
  ∀ k : ℕ, subseq f atf k ≤ f k := by
  intro k
  induction k with
  | zero => simp only [subseq, hf0, le_refl]
  | succ k ih =>
    simp only [subseq]
    if hcond : subseq f atf k = ⊥ then
      simp only [hcond, ↓reduceDIte, bot_le]
    else
    simp only [hcond, ↓reduceDIte]
    rcases subseq_prop0' f atf hfat hf0 (k+1) with ⟨jtilde,hjtilde⟩
    simp only [subseq, ge_iff_le, hcond, ↓reduceDIte] at hjtilde
    if hjt : jtilde = k+1 then
      exact le_of_eq <| hjt ▸ hjtilde.2
    else
    exact hjtilde.2 ▸ (hfat <| le_of_lt <| lt_of_le_of_ne hjtilde.1 <| Ne.symm hjt)

open Classical in
/-- `subseq_prop5` is the strict-decrease property for the normalised subsequence.

  Up to the index where `subseq f atf` first hits `⊥`, consecutive values are strictly decreasing.
  This is the key fact used later to turn antitonicity into a `StrictAnti` chain.
-/
lemma subseq_prop5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f) :
∀ (i j : ℕ), i < j → j ≤ Nat.find (subseq_prop1 f atf hfat hf0) →
  subseq f atf j < subseq f atf i := by
  intro i
  have : ∀ j : ℕ, i+1 ≤ j → j ≤ Nat.find (subseq_prop1 f atf hfat hf0) →
    subseq f atf j < subseq f atf i := by
    apply Nat.le_induction
    · intro h
      simp only [subseq]
      if hcond : subseq f atf i = ⊥ then
        simp only [hcond, ↓reduceDIte, lt_self_iff_false]
        exact (Nat.find_min (subseq_prop1 f atf hfat hf0) (Nat.lt_of_add_one_le h)) hcond
      else
      simp only [hcond, ↓reduceDIte]
      exact Nat.find_spec (subseq.pf2 f atf i (of_eq_false (eq_false hcond)))
    · intro j hij hind hj
      simp only [subseq]
      if hcond : subseq f atf j = ⊥ then
        simp only [hcond, ↓reduceDIte]
        apply bot_lt_iff_ne_bot.2
        by_contra!
        replace := le_trans hj <| Nat.find_min' (subseq_prop1 f atf hfat hf0) this
        linarith
      else
      simp only [hcond, ↓reduceDIte]
      if hcond' : j ≤ Nat.find (subseq_prop1 f atf hfat hf0) then
        exact lt_trans (Nat.find_spec (subseq.pf2 f atf j
          (of_eq_false (eq_false hcond)))) <| hind hcond'
      else
      by_contra!
      exact hcond <| le_bot_iff.1 <| (Nat.find_spec (subseq_prop1 f atf hfat hf0)) ▸
        subseq_prop2 f atf (le_of_lt <| lt_of_not_ge hcond')
  exact fun j hij hle ↦ this j hij hle

open Classical in
/-- `subseq_prop4` is a technical combinatorial lemma about the index where `subseq f atf` hits `⊥`.

  It shows that this index cannot coincide with a specified `k` under a mild “plateau” hypothesis
  (`∃ N, N+1 ≤ k ∧ f N = f (N+1)`). The proof uses a finite-cardinality argument on the image set
  `{f t | t ≤ k}`.
-/
lemma subseq_prop4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f) (k : ℕ) (hk : f k = ⊥)
(htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N + 1)) : (Nat.find <| subseq_prop1 f atf hfat hf0) ≠ k := by
  let A := Nat.find <| subseq_prop1 f atf hfat hf0
  let 𝒮 := {f t | (t ≤ k)}
  have helper : ∀ t : ℕ, ∃ l : ℕ, l ≤ k ∧ subseq f atf t = f l := by
    intro t
    if hcond : subseq f atf t = ⊥ then
      exact ⟨k,⟨le_rfl,hcond ▸ hk.symm⟩⟩
    else
    rcases subseq_prop0' f atf hfat hf0 t with ⟨l,hl1,hl2⟩
    exact ⟨l,⟨byContradiction fun this ↦ hcond (le_bot_iff.mp
      (hk ▸ hfat (le_of_lt (not_le.1 this))) ▸ hl2),hl2⟩⟩
  let Φ : Fin (A+1) → 𝒮 := fun d ↦ ⟨f (Nat.find (helper d)),
    Set.mem_setOf.mpr ⟨Nat.find (helper d),⟨(Nat.find_spec (helper d)).1,rfl⟩⟩⟩
  have hΦ : Function.Injective Φ := by
    intro d1 d2 h
    simp only [Subtype.mk.injEq, Φ, 𝒮] at h
    have := (Nat.find_spec (helper d2)).2.symm ▸ (Nat.find_spec (helper d1)).2.symm ▸ h
    if hd : d1 < d2 then
      exact False.elim <| (lt_self_iff_false (subseq f atf ↑d2)).mp <| this ▸
        subseq_prop5 f hf0 atf hfat d1 d2 hd (Fin.is_le d2)
    else
      if hd' : d2 < d1 then
        exact False.elim <| (lt_self_iff_false (subseq f atf ↑d2)).mp <| this ▸
          subseq_prop5 f hf0 atf hfat d2 d1 hd' (Fin.is_le d1)
      else
      exact Fin.le_antisymm (le_of_not_gt hd') (le_of_not_gt hd)
  let fS : Fin (k+1) → 𝒮 := fun n ↦ ⟨f n,Set.mem_setOf.mpr ⟨n,⟨Fin.is_le n,rfl⟩⟩⟩
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
/-- `subseq_prop6` transports a stepwise predicate from the original chain to the subsequence.

  Given a predicate `P` on strict steps of `f` (assumed for each `i < Nat.find atf`), the lemma
  produces the corresponding fact for each strict step of `subseq f atf` before it reaches `⊥`.
-/
lemma subseq_prop6 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat : Antitone f)
(P : {z : ℒ × ℒ // z.1 < z.2} → Prop)
(ho : ∀ i : ℕ, i < Nat.find atf → (hfi :f (i + 1) < f i) → P ⟨(f (i+1), f i),hfi⟩) :
∀ i : ℕ, (hi : i < Nat.find (subseq_prop1 f atf hfat hf0)) →
  P ⟨(subseq f atf (i + 1),subseq f atf i), subseq_prop5 f hf0 atf hfat i (i+1)
  (Nat.lt_succ_self i) (Nat.succ_le_iff.2 hi)⟩ := by
  intro i hi
  simp only [subseq]
  have hcond : subseq f atf i ≠ ⊥ := by
    by_contra!
    replace := Nat.find_min' (subseq_prop1 f atf hfat hf0) this
    linarith
  simp only [hcond, ↓reduceDIte]
  rcases subseq_prop0' f atf hfat hf0 i with ⟨j,⟨_,hj⟩⟩
  simp only [hj]
  rw [hj] at hcond
  have hcondnew : ∃ l : ℕ, f l < f j := by
    rcases atf with ⟨k,hk⟩
    use k
    rw [hk]
    (expose_names; exact Ne.bot_lt' (id (Ne.symm hcond_1)))
  let jtilde := Nat.find hcondnew
  expose_names
  have heq : Nat.find ((funext fun k ↦ congrArg (LT.lt (f k)) hj) ▸ subseq.pf2 f atf i
    (of_eq_false (eq_false hcond_1))) = (jtilde -1) +1:= by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
    by_contra!
    simp only [Nat.lt_one_iff, Nat.find_eq_zero] at this
    exact (not_lt_of_ge le_top) <| hf0 ▸ this
  have ha : f j = f (jtilde -1) := by
    have : ∀ j' : ℕ, j ≤ j' → j' < jtilde → f j' = f j := by
      apply Nat.le_induction
      · exact fun _ ↦ rfl
      · intro n hn hn' hn''
        by_contra!
        have := lt_of_le_of_lt (Nat.find_min' hcondnew <| lt_of_le_of_ne
          (hfat (Nat.le_add_right_of_le hn)) this) hn''
        linarith
    refine Eq.symm <| this (jtilde -1) ?_ (by linarith)
    by_contra!
    exact (lt_self_iff_false (f j)).mp <| lt_of_le_of_lt (hfat (Nat.le_of_pred_lt this))
      (Nat.find_spec hcondnew)
  conv =>
    arg 1; arg 1; arg 2;
    rw [ha]
  have yah : f jtilde < f (jtilde -1)  := lt_of_lt_of_eq (Nat.find_spec hcondnew) ha
  have : f (jtilde - 1 + 1) < f (jtilde - 1) := by
    conv_lhs =>
      arg 1;
      apply Nat.sub_one_add_one <| fun this ↦ (lt_self_iff_false ⊤).mp <| hf0 ▸
        lt_of_lt_of_le (this ▸ yah) le_top
    exact yah
  simpa only [← heq] using ho (jtilde -1) (byContradiction fun this' ↦
    not_le_of_gt (lt_of_le_of_lt bot_le yah) (Nat.find_spec atf ▸ hfat (le_of_not_gt this'))) this

/-- `μA_eq_μmin` is a small bridge lemma between two “minimal slope” constructions.

  It rewrites `μmin μ I` as the value `μA μ I` by applying Proposition 4.1 to the restricted slope
  `Resμ I μ`.
-/
lemma μA_eq_μmin {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
[SlopeLike μ] (I : {p : ℒ × ℒ // p.1 < p.2}) :
μmin μ I = μA μ I := by
  convert Eq.symm <| (proposition_4_1 (Resμ I μ) inferInstance inferInstance).1
  · simp only [μmin_res_intvl]
    rfl
  · unfold μAstar
    simp only [μA_res_intvl]
    rfl

open Classical in
/-- `μ_bot_JH_eq_μ_tot` is an invariance statement along a Jordan–Hölder filtration.

  For every index `i` before the terminal length, the payoff `μ (⊥, JH.filtration i)` equals the
  total payoff `μ (⊥, ⊤)`. The proof is by induction on `i` using the first step condition.
-/
lemma μ_bot_JH_eq_μ_tot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hsl : SlopeLike μ] (JH : JordanHolderFiltration μ) :
∀ i : ℕ, (hi : i < Nat.find JH.fin_len) → μ ⟨(⊥, JH.filtration i), by
  rw [← Nat.find_spec JH.fin_len]
  apply JH.strict_anti
  · exact hi
  · exact le_rfl
  ⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
  intro i hi
  induction i with
  | zero => simp only [JH.first_eq_top]
  | succ i hi' =>
    have := seesaw' μ hsl ⊥ (JH.filtration (i + 1)) ⊤ ⟨by
      rw [← Nat.find_spec JH.fin_len]
      apply JH.strict_anti
      · exact hi
      · exact le_rfl
      ,by
      rw [← JH.first_eq_top]
      apply JH.strict_anti
      · exact Nat.zero_lt_succ i
      · exact le_of_lt hi
      ⟩
    refine (this.2.2.2.2 ?_).1
    rw [← JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]
    if htop : JH.filtration i = ⊤ then
      simp only [htop]
    else
    have := seesaw' μ hsl (JH.filtration (i + 1)) (JH.filtration i) ⊤ ⟨by
      apply JH.strict_anti
      · exact lt_add_one i
      · exact Nat.le_of_succ_le hi
      ,Ne.lt_top' fun a ↦ htop (id (Eq.symm a))
      ⟩
    refine (this.2.2.2.1 ?_).1
    specialize hi' (Nat.lt_of_succ_lt hi)
    have := seesaw' μ hsl ⊥ (JH.filtration i) ⊤ ⟨by
      rw [← Nat.find_spec JH.fin_len]
      apply JH.strict_anti
      · exact Nat.lt_of_succ_lt hi
      · exact le_rfl
      ,Ne.lt_top' fun a ↦ htop (id (Eq.symm a))⟩
    rw [← (this.2.2.1 hi').2,JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]

open Classical in
/-- `semistable_of_step_cond₂` turns a strict step condition into semistability on each step.

  Assuming that for every intermediate `z` strictly between consecutive values
  `filtration (i+1) < z < filtration i` the slope strictly improves, the restricted slope
  `Resμ ⟨(filtration (i+1), filtration i), _⟩ μ` is semistable.
-/
lemma semistable_of_step_cond₂
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i),
      strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) → Semistable (Resμ ⟨(filtration (i+1), filtration i),
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
  intro h i hi
  have h := h i hi
  apply (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1)
    (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.2 (fun _ _ ↦ inferInstance)
  apply (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1)
    (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).1
  apply eq_of_le_of_ge ?_ ?_
  · apply sInf_le
    simp only [ne_eq, Set.mem_setOf_eq]
    use ⊥
    simp only [bot_ne_top, not_false_eq_true, and_true, exists_prop,in_TotIntvl]
  · apply le_sInf
    intro b hb
    simp only [ne_eq, Set.mem_setOf_eq] at hb
    rcases hb with ⟨u,hu1,hu2⟩
    rw [← hu2]
    simp only [μ_res_intvl]
    if hu : u = ⊥ then
      simp only [hu, le_refl]
    else
    have h := h u.val (lt_of_le_of_ne u.prop.1 (by
      by_contra hc
      refine hu ?_
      apply Subtype.coe_inj.1
      exact id (Eq.symm hc)
          )) (lt_of_le_of_ne u.prop.2 (by
            by_contra hc
            refine hu1.2 ?_
            apply Subtype.coe_inj.1
            exact hc
            ))
    have := ((seesaw' μ inferInstance (filtration (i + 1)) u.val (filtration i)
      ⟨(lt_of_le_of_ne u.prop.1 (by
      by_contra hc
      refine hu ?_
      apply Subtype.coe_inj.1
      exact id (Eq.symm hc)
          )),(lt_of_le_of_ne u.prop.2 (by
            by_contra hc
            refine hu1.2 ?_
            apply Subtype.coe_inj.1
            exact hc
            ))⟩).1.1 h).2
    apply le_of_lt this

open Classical in
/-- `stable_of_step_cond₂` upgrades the previous lemma from semistability to stability.

  Under the same strict step condition, each restricted slope on a step interval is not only
  semistable but satisfies the strict inequality required for `Stable`.
-/
lemma stable_of_step_cond₂
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i),
      strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) → Stable (Resμ ⟨(filtration (i+1), filtration i),
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
    intro h i hi
    refine {
      toSemistable := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi, stable := ?_
      }
    · intro x hx hx'
      have := (proposition_4_1 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i
        (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance).1
      have this' := (proposition_4_1 (Resμ ⟨(filtration (i+1), x.val), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ μ) inferInstance inferInstance).1
      unfold μAstar at this
      unfold μAstar at this'
      simp only [μA_res_intvl,μmin_res_intvl] at *
      rw [this]
      simp only [strip_bot <| strict_anti i (i + 1) (lt_add_one i) hi,
        strip_top <| lt_of_le_of_ne (Subtype.prop x).left
          fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc))),
        strip_bot <| lt_of_le_of_ne (Subtype.prop x).left
          fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc)))] at *
      rw [this']
      have hss := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi
      replace := (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1)
        (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.1 hss
      replace := (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti
        i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).2 this
      simp only [μmin_res_intvl,μ_res_intvl] at this
      simp only [strip_bot <| strict_anti i (i + 1) (lt_add_one i) hi,
        strip_top <| strict_anti i (i + 1) (lt_add_one i) hi] at *
      rw [this]
      apply ne_of_lt
      replace : μmin μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ ≤ μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ := by
        apply sInf_le
        simp only [ne_eq, Set.mem_setOf_eq]
        use filtration (i + 1)
        simp only [exists_prop, and_true]
        refine ⟨⟨le_rfl,x.prop.1⟩, ?_⟩
        by_contra hc
        refine hx ?_
        apply Subtype.coe_inj.1
        rw [← hc]
        rfl
      refine lt_of_le_of_lt this ?_
      exact (h i hi) x.val (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          )) <| lt_iff_le_not_ge.mpr (lt_top_iff_ne_top.2 hx')

open Classical in
/-- `step_cond₂_of_stable` is the converse direction: stability implies the strict step condition.

  If each restricted slope on the step intervals is stable, then for every strict intermediate
  `z` one has the strict inequality comparing `μ (filtration (i+1), z)` with the step value.
-/
lemma step_cond₂_of_stable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i):
(
∀ i : ℕ, (hi : i < Nat.find fin_len) → Stable (Resμ ⟨(filtration (i+1), filtration i),
  strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
)
→ (∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i),
      strict_anti i (i+1) (lt_add_one i) hi⟩
) := by
  intro hst i hi z hz hz'
  have hss := (hst i hi).toSemistable.semistable ⟨z, le_of_lt hz, le_of_lt hz'⟩ (by
    apply bot_lt_iff_ne_bot.1
    by_contra hc
    simp only [not_bot_lt_iff] at hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    rw [hc] at hz
    exact False.elim <| (lt_self_iff_false (filtration (i + 1))).mp hz
    )
  simp only [gt_iff_lt, not_lt] at hss
  have hst' := (hst i hi).stable ⟨z, le_of_lt hz, le_of_lt hz'⟩ (by
    apply bot_lt_iff_ne_bot.1
    by_contra hc
    simp only [not_bot_lt_iff] at hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    rw [hc] at hz
    exact False.elim <| (lt_self_iff_false (filtration (i + 1))).mp hz
    ) (by
      by_contra hc
      apply Subtype.coe_inj.2 at hc
      simp only at hc
      rw [hc] at hz'
      exact False.elim <| (lt_self_iff_false (filtration i)).mp hz'
    )
  have hst' := lt_of_le_of_ne hss hst'
  have := (proposition_4_1 (Resμ ⟨(filtration (i+1), filtration i),
    strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance).1
  unfold μAstar at this
  rw [this] at hst'
  have this' := (proposition_4_1 (Resμ ⟨(filtration (i+1), z), hz⟩ μ) inferInstance inferInstance).1
  unfold μAstar at this'
  have hb : μA (Resμ ⟨(filtration (i + 1), filtration i), gt_trans hz' hz⟩ μ)
    ⟨(⊥, ⟨z, le_of_lt hz, le_of_lt hz'⟩), by
  simp only
  by_contra hc
  simp only [not_bot_lt_iff] at hc
  apply Subtype.coe_inj.2 at hc
  simp only at hc
  rw [hc] at hz
  exact False.elim <| (lt_self_iff_false (filtration (i + 1))).mp hz⟩ =
    μA (Resμ ⟨(filtration (i + 1), z), hz⟩ μ) ⟨(⊥, ⊤), bot_lt_top⟩ := by
    simp only [μA_res_intvl,μmin_res_intvl] at *
    rfl
  rw [hb, this'] at hst'
  have := (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i),
    strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).2
    <| (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i)
    hi⟩ μ) inferInstance inferInstance inferInstance).2.1 (hst i hi).toSemistable
  rw [this] at hst'
  have := (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i
    (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 0 3).2 <|
    (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1)
    (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.1 (hst i hi).toSemistable
  simp only [μmin_res_intvl,μ_res_intvl] at hst'
  unfold μmax at this
  apply le_of_eq at this
  apply sSup_le_iff.1 at this
  simp only [ne_eq, Set.mem_setOf_eq, forall_exists_index, forall_and_index] at this
  have this_bak := this
  have := this (Resμ ⟨(filtration (i + 1), filtration i), gt_trans hz' hz⟩
    μ ⟨(⊥, ⟨z, le_of_lt hz, le_of_lt hz'⟩), by
  simp only
  by_contra hc
  simp only [not_bot_lt_iff] at hc
  apply Subtype.coe_inj.2 at hc
  simp only at hc
  rw [hc] at hz
  exact False.elim <| (lt_self_iff_false (filtration (i + 1))).mp hz⟩)
    ⟨z, le_of_lt hz, le_of_lt hz'⟩ (in_TotIntvl _) (by
    apply Ne.symm
    apply bot_lt_iff_ne_bot.1
    by_contra hc
    simp only [not_bot_lt_iff] at hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    rw [hc] at hz
    exact False.elim <| (lt_self_iff_false (filtration (i + 1))).mp hz
     ) rfl
  refine lt_of_le_of_ne this ?_
  by_contra hc
  simp only [strip_bot (gt_trans hz' hz), strip_top (gt_trans hz' hz)] at hst'
  rw [← hc] at hst'
  have t1 : ↑(@Bot.bot (Interval ⟨(filtration (i + 1), z), hz⟩) instBoundedOrderInterval.toBot :
    Interval ⟨(filtration (i + 1), z), hz⟩) = filtration (i + 1) := rfl
  have t2 : ↑(@Top.top (Interval ⟨(filtration (i + 1), z), hz⟩) instBoundedOrderInterval.toTop :
    Interval ⟨(filtration (i + 1), z), hz⟩) = z := rfl
  simp only [t1, t2] at hst'
  unfold μmin at hst'
  apply sInf_lt_iff.1 at hst'
  rcases hst' with ⟨s,⟨y,hy1,hy2⟩,hs⟩
  rw [← hy2] at hs
  have := ((seesaw' μ inferInstance (filtration (i + 1)) y z ⟨by
    refine lt_of_le_of_ne hy1.1.1 ?_
    by_contra hc
    simp only [hc, lt_self_iff_false] at hs
    ,lt_of_le_of_ne hy1.1.2 hy1.2⟩).2.1.2.2 hs).1
  simp only [hc, gt_iff_lt] at this
  have res := this_bak (Resμ ⟨(filtration (i + 1), filtration i), gt_trans hz' hz⟩
    μ ⟨(⊥, ⟨y,hy1.1.1,le_of_lt <| lt_of_le_of_lt hy1.1.2 hz'⟩), by
    refine lt_of_le_of_ne hy1.1.1 ?_
    by_contra hc
    simp only at hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    simp only [← hc, strip_bot (gt_trans hz' hz), lt_self_iff_false] at hs⟩)
      ⟨y,hy1.1.1,le_of_lt <| lt_of_le_of_lt hy1.1.2 hz'⟩ (in_TotIntvl _) (by
    by_contra hc
    apply Subtype.coe_inj.2 at hc
    simp only at hc
    simp [← hc, strip_bot (gt_trans hz' hz)] at hs
    ) rfl
  simp only [μ_res_intvl, strip_bot (gt_trans hz' hz), strip_top (gt_trans hz' hz)] at res
  exact (not_le_of_gt this) res

open Classical in
/-- `semistable_resμ_of_jordanHolderFiltration` deduces semistability for the final restriction.

  If the last nontrivial step of a Jordan–Hölder filtration lies strictly below `⊤`, then the
  restricted slope on the interval `(JH.filtration (len-1), ⊤)` is semistable.
-/
lemma semistable_resμ_of_jordanHolderFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ]
[StrongDescendingChainCondition' μ] [Affine μ] (JH : JordanHolderFiltration μ)
(h : JH.filtration (Nat.find JH.fin_len - 1) < ⊤) :
Semistable (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ) := by
  apply (thm4d21 (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ) inferInstance
    inferInstance inferInstance).2.2 (fun _ _ ↦ inferInstance)
  apply (List.TFAE.out (thm4d21 (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ)
    inferInstance inferInstance inferInstance).1 1 3).1
  rw [μmin_res_intvl, μ_res_intvl]
  simp only [μmin]
  apply eq_of_le_of_ge ?_ ?_
  · apply sInf_le
    simp only [ne_eq, Set.mem_setOf_eq]
    use JH.filtration (Nat.find JH.fin_len - 1), ⟨⟨le_rfl,le_top⟩,lt_top_iff_ne_top.1 h⟩
    rfl
  · apply le_sInf
    intro z hz
    simp only [ne_eq, Set.mem_setOf_eq] at hz
    rcases hz with ⟨u,⟨hu1,hu2⟩⟩
    rw [← hu2]
    have := (thm4d21 μ inferInstance inferInstance inferInstance).2.1 inferInstance
    replace := (List.TFAE.out (thm4d21 μ inferInstance inferInstance inferInstance).1 1 3).2 this
    have this' : μ ⟨(u,⊤),lt_top_iff_ne_top.2 hu1.2⟩ ≥ μ ⟨(⊥,⊤),bot_lt_top⟩ := by
      rw [← this]
      apply sInf_le
      use u, ⟨in_TotIntvl _,hu1.2⟩
    replace := μ_bot_JH_eq_μ_tot JH (Nat.find JH.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JH)
    rwa [((seesaw' μ inferInstance ⊥ (JH.filtration (Nat.find JH.fin_len - 1)) ⊤ ⟨by
      by_contra hc
      simp only [not_bot_lt_iff] at hc
      exact (Nat.find_min JH.fin_len <| Nat.sub_one_lt <| JH_pos_len JH) hc
      ,h⟩).2.2.1 this).2] at this'

/-- Intervals in a modular lattice inherit modularity.

  This instance transports `IsModularLattice` from `ℒ` to the interval type `Interval I`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [iml : IsModularLattice ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}} : IsModularLattice (Interval I) where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    apply iml.sup_inf_le_assoc_of_le
    exact hxz

open Classical in
/--
  `induction_on_length_of_JordanHolderFiltration` is the main internal induction principle.

  Fix `n`. Assuming there exists a Jordan–Hölder filtration of length `≤ n`, the lemma shows that
  every Jordan–Hölder filtration for the same slope function has length `≤ n`.

  This is proved by induction on `n`, using restriction to a final interval and modularity to
  compare lengths.
-/
lemma induction_on_length_of_JordanHolderFiltration : ∀ n : ℕ, ∀ ℒ : Type*, ∀ _: Nontrivial ℒ,
   ∀ _ : Lattice ℒ, ∀ _ : BoundedOrder ℒ, ∀ _ : WellFoundedGT ℒ,
∀ _ : IsModularLattice ℒ,
∀ S : Type*, ∀ _ : CompleteLinearOrder S, ∀ μ : {p : ℒ × ℒ // p.1 < p.2} → S,
∀ _ : FiniteTotalPayoff μ, ∀ _ : SlopeLike μ,
∀ _ : Semistable μ, ∀ _ : StrongDescendingChainCondition' μ, ∀ _ :
Affine μ, (∃ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≤ n) →
  (∀ JH' : JordanHolderFiltration μ, Nat.find JH'.fin_len ≤ n) := by
  intro n
  induction n with
  | zero =>
    intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hwdcc' affine ⟨JH,hJH⟩ JH'
    simp only [nonpos_iff_eq_zero, Nat.find_eq_zero, JH.first_eq_top, top_ne_bot] at hJH
  | succ n hn =>
    intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hwdcc' affine ⟨JHy,hJHy⟩ JHx
    if htriv : Nat.find JHx.fin_len = 1 then
      exact htriv ▸ Nat.le_add_left 1 n
    else
    have : 0 < Nat.find JHx.fin_len - 1 := by
      have h : Nat.find JHx.fin_len ≠ 0 := by
        intro h'
        simp only [Nat.find_eq_zero, JHx.first_eq_top, top_ne_bot] at h'
      omega
    let Ires : {p : ℒ × ℒ // p.1 < p.2} := ⟨(JHx.filtration (Nat.find JHx.fin_len - 1),⊤),
      (JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this
      (Nat.sub_le (Nat.find JHx.fin_len) 1)⟩
    have nt := (JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this
      (Nat.sub_le (Nat.find JHx.fin_len) 1)
    have ftpLres : FiniteTotalPayoff (Resμ Ires μ) := by
      refine { fin_tot_payoff := ?_ }
      simp only [Resμ]
      have := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
      simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this
      exact ((seesaw' μ hsl ⊥ (JHx.filtration <| Nat.find JHx.fin_len - 1) ⊤ ⟨bot_lt_iff_ne_bot.2 <|
        Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this).2 ▸
        hftp.fin_tot_payoff
    let JH_raw : ℕ → (Interval Ires) :=
      fun n ↦ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1)) ⊔ JHy.filtration n,⟨le_sup_left,le_top⟩⟩
    have JH_raw_antitone : Antitone JH_raw := by
      intro n1 n2 hn
      apply sup_le_sup_left <| JHy.antitone hn
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simp only [JH_raw, JHy.first_eq_top, le_top, sup_of_le_right, JH_raw]
      rfl
    have JH_raw_fin_len: JH_raw (Nat.find JHy.fin_len) = ⊥ := by
      simp only [JH_raw, Nat.find_spec JHy.fin_len, bot_le, sup_of_le_left, JH_raw]
      rfl
    let JHfinal := subseq JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simp only [JHfinal,subseq]
    have hcond1 : ∀ i < Nat.find (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩: ∃ k, JH_raw k = ⊥),
      ∀ (hfi : JH_raw (i + 1) < JH_raw i), (fun z ↦ Resμ Ires μ z =
      Resμ Ires μ ⟨(⊥, ⊤), bot_lt_top⟩) ⟨(JH_raw (i + 1), JH_raw i), hfi⟩ := by
      intro j hj hfj
      simp only [Resμ,JH_raw]
      have htrans : μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1),⊤),(JHx.first_eq_top) ▸
        JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)⟩ =
        μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        have := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this
        exact ((seesaw' μ hsl ⊥ (JHx.filtration <| Nat.find JHx.fin_len - 1) ⊤ ⟨bot_lt_iff_ne_bot.2
          <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this).2.symm
      have hj': ∀ j: ℕ, j ≤ Nat.find JHy.fin_len →
        μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j), lt_of_lt_of_le
        (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx)
        le_sup_left⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        refine fun j hj ↦ eq_of_le_of_ge ?_ ?_
        · have : Semistable μ → μmax μ TotIntvl = μ TotIntvl :=
            fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2
              ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
          rw [← this hst]
          apply le_sSup
          simp only [ne_eq, Set.mem_setOf_eq]
          use JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j, ⟨in_TotIntvl _,Ne.symm <|
            bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <|
            Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
        · have : μmin μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),
            lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <|
            JH_pos_len JHx) le_sup_left⟩ ≤
            μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le
            (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx)
            le_sup_left⟩ := by
            apply sInf_le
            simp only [ne_eq, Set.mem_setOf_eq]
            use ⊥, ⟨⟨le_rfl, le_of_lt <| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <|
              Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩,Ne.symm <|
              bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len
              <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
          refine le_trans ?_ this
          rw [μA_eq_μmin μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JHy.filtration j),
            lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len
            (Nat.sub_one_lt (JH_pos_len JHx)))) le_sup_left⟩]
          if hjbot : ⊥ = JHy.filtration j  then
            simp only [← hjbot, bot_le, sup_of_le_left]
            rw [← μA_eq_μmin μ]
            replace := JHx.step_cond₁ (Nat.find JHx.fin_len -1) (by omega)
            rw [← this]
            unfold μmin
            apply le_sInf
            intro b hb
            rcases hb with ⟨u,hu1,hu2⟩
            rw [← hu2]
            replace := JHx.step_cond₂ (Nat.find JHx.fin_len -1) (by omega) u
            simp only [Nat.sub_one_add_one <| JH_pos_len JHx, Nat.find_spec JHx.fin_len] at *
            if ubot : u = ⊥ then
              simp only [ubot]
              exact le_rfl
            else
              apply bot_lt_iff_ne_bot.2 at ubot
              replace := this ubot (lt_of_le_of_ne hu1.1.2 hu1.2)
              exact le_of_lt <| ((seesaw' μ hsl ⊥ u (JHx.filtration (Nat.find JHx.fin_len - 1))
                ⟨ubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩).1.1 this).2
          else
          replace := (proposition_2_8 μ inferInstance (JHx.filtration (Nat.find JHx.fin_len - 1))
            (JHy.filtration j) ⊥ ⟨bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt
            (JH_pos_len JHx))),bot_lt_iff_ne_bot.2 fun a ↦ hjbot (id (Eq.symm a))⟩).1
          convert this.le
          have t1 : μ TotIntvl = μA μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1)),
            bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx)))⟩:= by
            rw [← μA_eq_μmin μ]
            have hess := μ_bot_JH_eq_μ_tot JHx (Nat.find JHx.fin_len -1) (by omega)
            rw [← hess]
            unfold μmin
            refine eq_of_le_of_ge ?_ ?_
            · apply le_sInf
              intro h hb
              simp only [ne_eq, Set.mem_setOf_eq] at hb
              rcases hb with ⟨u,hu1,hu2⟩
              rw [← hu2]
              if hubot : u = ⊥ then
                simp only [hubot, le_refl]
              else
              by_contra hc
              simp only [not_le] at hc
              replace := seesaw' μ hsl ⊥ u (JHx.filtration (Nat.find JHx.fin_len - 1))
                ⟨bot_lt_iff_ne_bot.2 hubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩
              replace hc := (this.2.1.2.2 hc).1
              rw [hess] at hc
              replace := (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2
                ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 hst)
              have this' : μ ⟨(⊥, u), bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μmax μ TotIntvl := by
                apply le_sSup
                simp only [ne_eq, Set.mem_setOf_eq]
                use u, ⟨in_TotIntvl _,Ne.symm hubot⟩
              exact (not_le_of_gt hc (this ▸ this')).elim
            · apply sInf_le
              simp only [ne_eq, Set.mem_setOf_eq]
              use ⊥
              simp only [exists_prop, and_true]
              refine ⟨⟨le_rfl,bot_le⟩, ?_⟩
              by_contra hc
              replace := (Nat.find_spec JHx.fin_len) ▸ JHx.strict_anti (Nat.find JHx.fin_len -1)
                (Nat.find JHx.fin_len) (by omega) le_rfl
              exact lt_irrefl _ <| hc.symm ▸ this
          have t2 : μ TotIntvl = μA μ ⟨(⊥, JHy.filtration j), bot_lt_iff_ne_bot.2
            fun a ↦ hjbot (id (Eq.symm a))⟩ := by
            rw [← μA_eq_μmin μ]
            have hess := μ_bot_JH_eq_μ_tot JHy j (by
              refine lt_of_le_of_ne hj ?_
              by_contra hc
              exact hjbot (hc ▸ Nat.find_spec JHy.fin_len).symm
            )
            rw [← hess]
            unfold μmin
            refine eq_of_le_of_ge ?_ ?_
            · apply le_sInf
              intro h hb
              simp only [ne_eq, Set.mem_setOf_eq] at hb
              rcases hb with ⟨u,hu1,hu2⟩
              rw [← hu2]
              if hubot : u = ⊥ then
                simp only [hubot, le_refl]
              else
              by_contra hc
              simp only [not_le] at hc
              replace := seesaw' μ hsl ⊥ u (JHy.filtration j)
                ⟨bot_lt_iff_ne_bot.2 hubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩
              replace hc := (this.2.1.2.2 hc).1
              rw [hess] at hc
              replace := (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2
                ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 hst)
              have this' : μ ⟨(⊥, u), bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μmax μ TotIntvl := by
                apply le_sSup
                simp only [ne_eq, Set.mem_setOf_eq]
                use u, ⟨in_TotIntvl _,Ne.symm hubot⟩
              exact (not_le_of_gt hc (this ▸ this')).elim
            · apply sInf_le
              simp only [ne_eq, Set.mem_setOf_eq]
              use ⊥
              simpa only [exists_prop, and_true] using ⟨⟨le_rfl,bot_le⟩,hjbot⟩
          rw [← t1,← t2]
          exact Eq.symm (min_self (μ TotIntvl))
      have tj1 := hj' j (le_of_lt <| lt_of_lt_of_le hj <|
        Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)
      have := tj1 ▸ ((seesaw' μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration
        (j+1)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j) ⟨lt_of_lt_of_le
        (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx)
        le_sup_left,lt_iff_le_not_ge.mpr hfj⟩).2.2.1 <| tj1 ▸ hj' (j+1) (lt_of_lt_of_le hj <|
        Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥)
        JH_raw_fin_len)).2
      rw [← this]
      exact id (Eq.symm htrans)
    let JH_FINAL : JordanHolderFiltration (Resμ Ires μ) := by
      refine JordanHolderFiltration.mk JHfinal
        (subseq_prop2 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩))
        (subseq_prop1 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
          JH_raw_antitone JH_raw_first_top)
        (fun i j hij hj ↦ subseq_prop5 JH_raw JH_raw_first_top
          (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone i j hij hj)
        (by simp only [JHfinal_first_top])
        (fun k1 hk1 ↦ subseq_prop6 JH_raw JH_raw_first_top
          (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun z ↦ (Resμ Ires μ) z =
          (Resμ Ires μ) ⟨(⊥,⊤),bot_lt_top⟩) hcond1 k1 hk1)
        ?_
      · refine fun i hi ↦ subseq_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len
          ⟩) JH_raw_antitone (fun w ↦ ∀ z : (Interval Ires), (hw : w.val.1 < z) → z < w.val.2 →
          (Resμ Ires μ) ⟨(w.val.1,z),hw⟩ < (Resμ Ires μ) w ) (fun j hj hfj w hw1 hw2 ↦
          ((seesaw' μ hsl ↑(JH_raw (j + 1)) w ↑(JH_raw j) ⟨lt_iff_le_not_ge.mpr hw1,
          lt_iff_le_not_ge.mpr hw2⟩).1.2.2 ?_).1) i hi
        have := hcond1 j hj hfj; simp only [Resμ] at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        replace this' := ((seesaw' μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤
          ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <|
          JH_pos_len JHx,nt⟩).2.2.1 this').2
        rw [this]
        have hproblem : JHy.filtration (j + 1) ≠ JHy.filtration j ⊓ ↑w := by
          by_contra hc
          simp only [JH_raw] at hw1
          have hw1 := lt_iff_le_not_ge.mpr hw1
          simp only [JH_raw] at hw2
          have hw2 := lt_iff_le_not_ge.mpr hw2
          have := @hmod.sup_inf_le_assoc_of_le (JHx.filtration (Nat.find JHx.fin_len - 1))
            (JHy.filtration j) w.val (by
            apply le_of_lt <| lt_of_le_of_lt le_sup_left hw1
            )
          rw [← hc, inf_eq_right.2 <| le_of_lt hw2] at this
          exact (not_le_of_gt hw1) this
        have hnle : ¬ (JHy.filtration j ≤ w) := by
          by_contra hc
          simp only [JH_raw] at hw2
          refine (not_le_of_gt hw2) ?_
          apply sup_le_iff.2
          refine ⟨?_,hc⟩
          simp only [JH_raw] at hw1
          have hw1 : JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JHy.filtration (j + 1) < w.val:= by
            exact lt_iff_le_not_ge.mpr hw1
          apply le_of_lt <| lt_of_le_of_lt le_sup_left hw1
        have heqs : μ ⟨(↑w, ↑(JH_raw j)), lt_iff_le_not_ge.mpr hw2⟩ =
          μ ⟨(JHy.filtration j ⊓ w,JHy.filtration j),inf_lt_left.2 hnle⟩ := by
          rw [affine.affine (JHy.filtration j) w.val hnle]
          have : ↑(JH_raw j) = JHy.filtration j ⊔ w.val := by
            simp only [JH_raw]
            apply eq_of_le_of_ge ?_ ?_
            · simp only [JH_raw] at hw1
              replace hw1 := lt_iff_le_not_ge.mpr hw1
              replace hw1 := sup_le_sup_right (le_of_lt hw1) (JHy.filtration j)
              replace := left_eq_sup.2 <| JHy.antitone (Nat.le_add_right j 1)
              rw [sup_comm] at this
              rw [sup_assoc, ← this] at hw1
              nth_rw 2 [sup_comm] at hw1
              exact hw1
            · simp only [JH_raw] at hw2
              replace hw2 := lt_iff_le_not_ge.mpr hw2
              replace hw2 := sup_le_sup_right (le_of_lt hw2) (JHy.filtration j)
              nth_rw 1 [sup_assoc,sup_comm] at hw2
              simp only [Nat.find_le_iff, forall_exists_index, and_imp, Nat.lt_find_iff, ne_eq,
                le_refl, sup_of_le_left, sup_le_iff, le_sup_right, true_and, ge_iff_le, JH_raw] at *
              exact hw2
          simp only [this]
        rw [heqs,((by rfl):μ ⟨(↑(⊥: Interval Ires), ↑(⊤: Interval Ires)), nt⟩ =
          μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1), ⊤), nt⟩),← this',← JHy.step_cond₁ j <|
          lt_of_lt_of_le hj <| Nat.find_le JH_raw_fin_len]
        have hlt : JHy.filtration (j+1) < JHy.filtration j ⊓ w := by
          refine lt_of_le_of_ne (le_inf (JHy.antitone <| Nat.le_add_right j 1) ?_) hproblem
          simp only [sup_comm, JH_raw] at hw1
          exact le_of_lt <| lt_of_le_of_lt (le_sup_left) <| lt_iff_le_not_ge.mpr hw1
        refine ((seesaw' μ hsl (JHy.filtration (j+1)) (JHy.filtration j ⊓ w) (JHy.filtration j)
          ⟨hlt,inf_lt_left.2 hnle⟩).1.1 ?_).2
        exact JHy.step_cond₂ j (by
          replace this' :=
            Nat.find_min (Exists.intro (Nat.find JHy.fin_len) JH_raw_fin_len : ∃ k, JH_raw k = ⊥) hj
          unfold JH_raw at this'
          by_contra hcontra
          push_neg at hcontra
          replace : JHy.filtration j = ⊥ :=
            le_bot_iff.mp <| (Nat.find_spec JHy.fin_len) ▸ JHy.antitone hcontra
          rw [this] at this'
          simp only [bot_le, sup_of_le_left] at this'
          exact this' rfl
          ) (JHy.filtration j ⊓ w) hlt <| inf_lt_left.mpr hnle
    have ha : Nat.find JH_FINAL.fin_len < Nat.find JHy.fin_len := by
      have : JHfinal (Nat.find JHy.fin_len) = ⊥ := by
        simp only [JHfinal]
        have : JH_raw (Nat.find JHy.fin_len) = ⊥ := by
          simp only [JH_raw, Nat.find_spec JHy.fin_len, bot_le, sup_of_le_left, JH_raw]
          rfl
        have hweird := eq_bot_iff.2 <| this ▸ subseq_prop3 JH_raw JH_raw_first_top
          (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len)
        exact hweird
      refine lt_of_le_of_ne (Nat.find_min' JH_FINAL.fin_len this) ?_
      · let i0 := Nat.findGreatest (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤
          JHy.filtration n) (Nat.find JHy.fin_len -1)
        refine subseq_prop4 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
          JH_raw_antitone (Nat.find JHy.fin_len) JH_raw_fin_len ⟨i0,⟨Nat.add_le_of_le_sub
          (Nat.one_le_iff_ne_zero.mpr <| JH_pos_len JHy) <| Nat.findGreatest_le
          (Nat.find JHy.fin_len -1),?_⟩⟩
        · replace := @Nat.findGreatest_spec 0 (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤
            JHy.filtration n) inferInstance (Nat.find JHy.fin_len -1) (zero_le _)
            (by simp only [JHy.first_eq_top, le_top])
          have h1 : JH_raw (i0 + 1) = JHy.filtration i0 := by
            refine eq_of_le_of_not_lt (sup_le this <| JHy.antitone (Nat.le_add_right i0 1))
              <| fun hc ↦ ?_
            replace : i0 ≤ Nat.find JHy.fin_len - 1 := Nat.findGreatest_le (Nat.find JHy.fin_len -1)
            have hsmall : JHy.filtration (i0 + 1) < ↑(JH_raw (i0 + 1)) := by
              refine lt_of_le_of_ne le_sup_right ?_
              · by_contra hcon
                have this' := right_eq_sup.1 hcon
                if hw : i0 + 1 ≤ Nat.find JHy.fin_len -1 then
                  exact @Nat.findGreatest_is_greatest (i0+1)
                    (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n)
                    inferInstance (Nat.find JHy.fin_len -1) (lt_add_one _) hw this'
                else
                  replace : i0 + 1 = Nat.find JHy.fin_len := by
                    replace : i0 + 1 ≤ Nat.find JHy.fin_len := (Eq.symm <| Nat.sub_one_add_one <|
                      JH_pos_len JHy) ▸ (by omega : i0 + 1 ≤ Nat.find JHy.fin_len - 1 + 1)
                    omega
                  simp only [this, Nat.find_spec JHy.fin_len, le_bot_iff] at this'
                  exact Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx) this'
            have otherwise := JHy.step_cond₂ i0 ((Nat.le_sub_one_iff_lt <| zero_lt_iff.2 <|
              JH_pos_len JHy).1 this) ↑(JH_raw (i0 + 1)) hsmall hc
            rw [JHy.step_cond₁ i0 <| lt_of_le_of_lt this <| Nat.sub_one_lt <| JH_pos_len JHy ]
              at otherwise
            refine (lt_iff_not_ge.1 otherwise) ?_
            rw [← JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)]
            simp only [Nat.sub_one_add_one <| JH_pos_len JHx]
            have himp : ¬ JHx.filtration (Nat.find JHx.fin_len - 1) ≤ JHy.filtration (i0+1) := by
              if hw : i0 + 1 ≤ Nat.find JHy.fin_len -1 then
                exact Nat.findGreatest_is_greatest (lt_add_one _) hw
              else
                replace : i0 + 1 = Nat.find JHy.fin_len := by
                  replace : i0 + 1 ≤ Nat.find JHy.fin_len := (Eq.symm <| Nat.sub_one_add_one <|
                    JH_pos_len JHy) ▸ (by omega : i0 + 1 ≤ Nat.find JHy.fin_len - 1 + 1)
                  omega
                simp only [this, Nat.find_spec JHy.fin_len, le_bot_iff, ne_eq]
                exact Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx)
            rw [(affine.affine (JHx.filtration (Nat.find JHx.fin_len - 1))
              (JHy.filtration (i0+1)) himp).symm]
            if hif : JHx.filtration (Nat.find JHx.fin_len) =
              JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1) then
              simp only [hif]
              exact le_rfl
            else
              have hh : JHx.filtration (Nat.find JHx.fin_len) <
                JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1) := by
                simp only [Nat.find_spec JHx.fin_len] at *
                exact Ne.bot_lt' hif
              replace := le_of_lt <| JHx.step_cond₂ (Nat.find JHx.fin_len -1)
                (Nat.sub_one_lt <| JH_pos_len JHx) (JHx.filtration (Nat.find JHx.fin_len -1) ⊓
                JHy.filtration (i0 + 1)) ((Nat.sub_one_add_one <| JH_pos_len JHx) ▸ hh)
                <| inf_lt_left.mpr himp
              simp only [Nat.sub_one_add_one <| JH_pos_len JHx] at this
              exact byContradiction fun hcc ↦  (lt_iff_not_ge.1 <| ((seesaw' μ hsl (JHx.filtration
                (Nat.find JHx.fin_len)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration
                (i0 + 1)) (JHx.filtration (Nat.find JHx.fin_len -1))
                ⟨hh,inf_lt_left.mpr himp⟩).2.1.2.2 <| lt_of_not_ge hcc).1) this
          exact Subtype.coe_inj.1 <| h1 ▸ (sup_eq_right.2 this)
    let JHfun : ℕ → Interval Ires := fun n ↦
      if hn : n ≤ Nat.find JHx.fin_len - 1 then
        ⟨JHx.filtration n,⟨JHx.antitone hn,le_top⟩⟩
      else
        ⊥
    have JHfun_fin_len : ∃ N : ℕ, JHfun N = ⊥ := by
        simp only [JHfun]
        use Nat.find JHx.fin_len
        simp only [lt_iff_not_ge.1 <| Nat.sub_one_lt <| JH_pos_len JHx, ↓reduceDIte]
    have JHfun_antitone : Antitone JHfun := by
        intro n1 n2 hn
        by_cases h3 : n2 ≤ Nat.find JHx.fin_len - 1
        · simp only [JHfun,le_trans hn h3,
            h3, ↓reduceDIte]
          exact JHx.antitone hn
        · simp only [h3, ↓reduceDIte, bot_le, JHfun]
    have hhard : Nat.find JHfun_fin_len = Nat.find JHx.fin_len - 1 := by
      have hgreat : Nat.find JHfun_fin_len ≤ Nat.find JHx.fin_len - 1 := by
        refine Nat.find_min' JHfun_fin_len ?_
        unfold JHfun
        simp only [le_refl, ↓reduceDIte]
        rfl
      refine eq_of_le_of_not_lt hgreat fun hv ↦ ?_
      have hweired : JHx.filtration (Nat.find JHfun_fin_len) =
        JHx.filtration (Nat.find JHx.fin_len - 1)  := by
        have this' := Nat.find_spec JHfun_fin_len
        unfold JHfun at this'
        rw [dif_pos hgreat] at this'
        apply Subtype.coe_inj.2 at this'
        exact this'
      exact (lt_self_iff_false (JHx.filtration (Nat.find JHx.fin_len - 1))).1 <|
        hweired ▸ JHx.strict_anti (Nat.find JHfun_fin_len) (Nat.find JHx.fin_len - 1) hv <|
        Nat.sub_le (Nat.find JHx.fin_len) 1
    let JHres : JordanHolderFiltration (Resμ Ires μ) := by
      refine JordanHolderFiltration.mk
        JHfun JHfun_antitone JHfun_fin_len (fun i j hij hj ↦ ?_) ?_ ?_ ?_
      · simp only [JHfun,hhard ▸ hj,le_of_lt <| lt_of_lt_of_le hij (hhard ▸ hj),dif_pos]
        have := JHx.strict_anti i j hij (le_trans (hhard ▸ hj) <|
          le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        refine lt_iff_le_and_ne.mpr ⟨Subtype.coe_le_coe.1 <| le_of_lt this,fun hu ↦ ?_⟩
        apply Subtype.coe_inj.2 at hu
        simp only at hu
        exact (lt_self_iff_false (JHx.filtration i)).mp <| hu ▸ this
      · simp only [JHfun, zero_le, ↓reduceDIte, JHx.first_eq_top]
        rfl
      · intro k1 hk1
        simp only [Resμ, JHfun]
        replace hk1 := hhard ▸ hk1
        have hk1' : k1 + 1 ≤ Nat.find JHx.fin_len - 1 := hk1
        simp only [hk1',le_of_lt hk1]
        simp only [↓reduceDIte]
        have := JHx.step_cond₁ k1 <| Nat.lt_of_lt_pred hk1
        simp only at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JHx)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        have ntop : JHx.filtration (Nat.find JHx.fin_len - 1) < ⊤ := by
          replace : Nat.find JHx.fin_len - 1 ≠ 0 := by
            by_contra t
            rw [t] at hk1
            exact Nat.not_succ_le_zero k1 hk1
          rw [← JHx.first_eq_top]
          exact JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) (by (expose_names; exact this_1))
            (le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        exact this ▸ (((seesaw' μ) inferInstance ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤
          ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len (Nat.sub_one_lt <|
          JH_pos_len JHx),ntop⟩).2.2.1 this').2
      · intro i hi z hz hz'
        simp only [Resμ]
        have htemp : JHx.filtration (i + 1) < z.val := by
          simp only [JHfun,Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi] at hz
          exact lt_iff_le_not_ge.mpr hz
        have htemp2 : z < JHx.filtration i := by
          simp only [JHfun,le_of_lt <| hhard ▸ hi] at hz'; simp only [↓reduceDIte] at hz'
          exact lt_iff_le_not_ge.mpr hz'
        simp only [JHfun]; simp only [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi,
          ↓reduceDIte, le_of_lt <| hhard ▸ hi, gt_iff_lt]
        exact JHx.step_cond₂ i (Nat.lt_of_lt_pred <| hhard ▸ hi) z htemp htemp2
    exact Nat.le_add_of_sub_le <| hhard ▸ hn (Interval Ires) inferInstance inferInstance
      inferInstance inferInstance inferInstance S clo (Resμ Ires μ) ftpLres inferInstance
      (semistable_resμ_of_jordanHolderFiltration _ _) inferInstance inferInstance
      ⟨JH_FINAL,Nat.le_of_lt_succ <| Nat.lt_of_lt_of_le ha hJHy⟩ JHres


end impl

end HarderNarasimhan
