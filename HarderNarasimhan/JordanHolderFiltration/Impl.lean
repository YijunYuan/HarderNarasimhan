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
open Classical

namespace HarderNarasimhan

namespace impl
noncomputable def JHFil {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc n ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}
    if h𝒮 : 𝒮.Nonempty then
      (hacc.wf.has_min 𝒮 h𝒮).choose
    else
      ⊥


lemma JHFil_anti_mono {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ, JHFil μ hμ hμsl hst hdc k > ⊥ → JHFil μ hμ hμsl hst hdc k > JHFil μ hμ hμsl hst hdc (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simp only [h]
    exact hk


lemma JHFil_prop₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1),JHFil μ hμ hμsl hst hdc k),JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
  intro k
  induction' k with k hk
  . intro hk'
    simp only [JHFil]
    by_cases this : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · simp only [this]
      have this' := (hacc.wf.has_min _ this).choose_spec.1.2.2
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ this).choose ⊤ ⟨(hacc.wf.has_min _ this).choose_spec.1.choose,(hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.1⟩) (by aesop)) (by aesop)).2.symm
    · simp only [this, ↓reduceDIte]
  · intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this, Set.not_nonempty_empty, ↓reduceDIte, gt_iff_lt,
        lt_self_iff_false] at hk'
    have jh_kp1_ntop' : JHFil μ hμ hμsl hst hdc k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil,jh_kp1_ntop]
      exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
    have bot_jh_kp1_eq_ans := (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.2.2
    by_cases jh_kp2_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc (k + 1) ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · have smart : μ ⟨(⊥, (hacc.wf.has_min _ jh_kp2_ntop).choose), (hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.1⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ := by
        rw [(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.2,← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop ]
        simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp, forall_exists_index,
          ↓reduceDIte]
      have hfinal : μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ = μ ⟨((hacc.wf.has_min _ jh_kp2_ntop).choose, JHFil μ hμ hμsl hst hdc (k + 1)), (hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.1⟩ := by
        refine (Or.resolve_left ((Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ jh_kp2_ntop).choose (JHFil μ hμ hμsl hst hdc (k + 1)) ⟨(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose,(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.1⟩) (?_)) (?_)).2
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [smart]; simp only [JHFil,jh_kp1_ntop]
          simp only [↓reduceDIte,
            exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp, forall_exists_index,
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
      simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
        forall_exists_index] at hfinal
      rw [← hfinal]
      simp only [JHFil,jh_kp1_ntop]
      simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
        forall_exists_index]
      simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
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
          have : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k-1) ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
            by_contra hthis
            rw [this] at jh_kp1_ntop'
            simp only [JHFil,hthis] at jh_kp1_ntop'; simp only [↓reduceDIte, gt_iff_lt,
              lt_self_iff_false] at jh_kp1_ntop'
          simp only [JHFil,this]
          simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
            forall_exists_index]
          have := (hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.2
          simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
            forall_exists_index] at this
          exact this
      simp only [← this']
      have : JHFil μ hμ hμsl hst hdc (k + 1) < JHFil μ hμ hμsl hst hdc k := by
        simp only [JHFil,jh_kp1_ntop]
        exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
      have this'' :  μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ = μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), JHFil μ hμ hμsl hst hdc k), this⟩ := by
        rw [hk jh_kp1_ntop',← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop]
        simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
          forall_exists_index]
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst hdc (k + 1)) (JHFil μ hμ hμsl hst hdc k) ⟨hk',this⟩) (fun this_1 ↦ ne_of_lt (lt_trans this_1.left this_1.right) this'')) (fun this_1 ↦ ne_of_lt (gt_trans this_1.1 this_1.2) (Eq.symm this''))).1


lemma JHFil_fin_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∃ N : ℕ, JHFil μ hμ hμsl hst hdc N = ⊥ := by
  by_contra hc
  simp only [not_exists] at hc
  rcases hdc (fun n => JHFil μ hμ hμsl hst hdc n) <| strictAnti_of_add_one_lt <| fun n _ ↦ JHFil_anti_mono μ hμ hμsl hst hdc n (bot_lt_iff_ne_bot.2 <| hc n) with ⟨N, hN⟩
  exact hμ.symm <| hN ▸ JHFil_prop₁ μ hμ hμsl hst hdc N (bot_lt_iff_ne_bot.2 <| hc N)


lemma JHFil_prop₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [hwdcc' : StrongDescendingChainCondition' μ]
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → ∀ z : ℒ, (h' : JHFil μ hμ hμsl hst hdc (k + 1) < z) → (h'' : z < JHFil μ hμ hμsl hst hdc k) →
  μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), z), h'⟩ < μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), JHFil μ hμ hμsl hst hdc k), JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ := by
  intro k hk z h' h''
  have this_new : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
    exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hμsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hμsl inferInstance inferInstance).2.1 a)
  have this_new := this_new hst
  simp only [μmax, TotIntvl, ne_eq] at this_new
  have this_q: μ ⟨(⊥, z), lt_of_le_of_lt bot_le h'⟩ ≤ μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    rw [← this_new]
    apply le_sSup
    use z, ⟨in_TotIntvl z, Ne.symm <| bot_lt_iff_ne_bot.1 <| lt_of_le_of_lt bot_le h'⟩
  by_cases hfp1bot : JHFil μ hμ hμsl hst hdc (k + 1) = ⊥
  · simp only [hfp1bot]
    have : ¬ {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this] at hfp1bot
      have := (hacc.wf.has_min _ this).choose_spec.1.out.choose
      simp only [↓reduceDIte, exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp,
        forall_exists_index] at hfp1bot
      simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp, forall_exists_index] at this
      exact (ne_of_lt this) hfp1bot.symm
    apply Set.not_nonempty_iff_eq_empty.1 at this
    apply Set.eq_empty_iff_forall_notMem.1 at this
    have := this z
    simp only [exists_and_left, Set.mem_setOf_eq, not_and, not_exists] at this
    have := lt_of_le_of_ne this_q <| this h'' (lt_of_le_of_lt bot_le h')
    by_cases hk' : k = 0
    · simp only [hk',JHFil]
      exact this
    · conv_rhs =>
        arg 1; arg 1; arg 2; arg 6
        rw [← Nat.sub_one_add_one hk']
      have hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k - 1) ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
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
      simp only [exists_and_left, Set.mem_setOf_eq, gt_iff_lt, and_imp, forall_exists_index] at this
      exact this
  · have h''' : μ ⟨(⊥, z), lt_of_le_of_lt bot_le h'⟩ < μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
      refine lt_of_le_of_ne this_q ?_
      by_contra!
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · have := (hacc.wf.has_min _ hne).choose_spec.2 z (by use lt_of_le_of_lt bot_le h')
        simp only [JHFil,hne] at h'
        simp only [gt_iff_lt, exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this h'
      · refine hne ?_
        use z, lt_of_le_of_lt bot_le h'
    have h'''' : μ ⟨(⊥, ⊤), bot_lt_top⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · simp only [JHFil,hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp only [gt_iff_lt, exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index,
          ↓reduceDIte] at *
        exact this.symm
      · simp only [JHFil,hne] at hfp1bot
        simp only [↓reduceDIte, not_true_eq_false] at hfp1bot
    exact (JHFil_prop₁ μ hμ hμsl hst hdc k hk ).symm ▸ lt_trans ((Or.resolve_right <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst hdc (k + 1)) z ⟨bot_lt_iff_ne_bot.2 hfp1bot,h'⟩) (not_and_iff_not_or_not.2 <| Or.inl <| not_lt_of_lt <| h'''' ▸ h''')) (not_and_iff_not_or_not.2 <| Or.inl <| ne_of_gt <| h'''' ▸ h''')).2 h'''


lemma JH_pos_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} : ∀ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≠ 0 := by
  intro JH h
  simp only [Nat.find_eq_zero, JH.first_eq_top, top_ne_bot] at h


noncomputable def function_wrapper {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : ℕ → ℒ := fun n ↦
  match n with
  | 0 => ⊤
  | t + 1 =>
    if hcond : function_wrapper f atf t = ⊥ then
      ⊥
    else
      f <| Nat.find (⟨atf.choose,atf.choose_spec.symm ▸ bot_lt_iff_ne_bot.2 hcond⟩: ∃ k : ℕ, f k < function_wrapper f atf t)


lemma function_wrapper_prop0 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∀ i : ℕ, ∃ j : ℕ, f i = function_wrapper f atf j := by
  intro i
  induction' i with i hi
  · exact ⟨0,hf0⟩
  · rcases hi with ⟨j,hj⟩
    if h : f i = ⊥ then
      use j
      rw [← hj,h]
      exact le_bot_iff.1 <| h ▸ hf (Nat.le_succ i)
    else
    if h' : f i = f (i+1) then
      exact ⟨j,h' ▸ hj⟩
    else
      use j+1
      simp only [function_wrapper,hj ▸ h]
      simp only [↓reduceDIte]
      have hq := function_wrapper._proof_6 f atf j (Eq.mpr_not (eq_false (hj ▸ h)) (of_eq_false (Eq.refl False)))
      have : i + 1 = Nat.find hq := by
        apply eq_of_le_of_le
        · have : Nat.find hq > i := by
            by_contra hu
            apply le_of_not_gt at hu
            have hg := hj ▸ lt_of_le_of_lt (hf hu) (Nat.find_spec hq)
            exact (lt_self_iff_false (function_wrapper f atf j)).mp hg
          exact this
        · by_contra!
          exact (hj ▸ Nat.find_min hq this) <| lt_of_le_of_ne (hf <| Nat.le_succ i) <| Ne.symm h'
      exact congrArg f this


lemma function_wrapper_prop0' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∀ i : ℕ, ∃ j : ℕ, j ≥ i ∧ function_wrapper f atf i = f j:= by
  intro i
  induction' i with i hi
  · use 0
    simp only [function_wrapper, ge_iff_le, le_refl, and_self, hf0]
  · simp only [function_wrapper]
    if hcond : function_wrapper f atf i = ⊥ then
      simp only [ge_iff_le, hcond, ↓reduceDIte]
      rcases hi with ⟨t,ht⟩
      rw [hcond] at ht
      use t + 1
      simp only [add_le_add_iff_right, true_and, ht]
      exact ht.2 ▸ (Eq.symm <| le_bot_iff.1 <| ht.2 ▸ hf (Nat.le_succ t))
    else
    simp only [ge_iff_le, hcond, ↓reduceDIte]
    have hq := function_wrapper._proof_6 f atf i (of_eq_false (eq_false hcond))
    rcases hi with ⟨t,ht⟩
    rw [ht.2] at hq
    use Nat.find hq
    constructor
    · have : Nat.find hq > t := by
        by_contra d
        apply le_of_not_lt at d
        if hy: Nat.find hq = t then
          exact (lt_self_iff_false (f t)).mp (Eq.mp (congrArg (fun _a ↦ f _a < f t) hy) <| Nat.find_spec hq)
        else
        exact (lt_self_iff_false (f <| Nat.find hq)).1 <| lt_of_lt_of_le (Nat.find_spec hq) <| hf <| le_of_lt <| lt_of_le_of_ne d hy
      linarith
    simp only [ht]

lemma function_wrapper_prop1 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∃ N : ℕ, function_wrapper f atf N = ⊥ := by
  rcases (function_wrapper_prop0 f atf hf hf0 atf.choose) with ⟨N,hN⟩
  exact ⟨N, hN ▸ atf.choose_spec⟩

lemma function_wrapper_prop2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : Antitone (function_wrapper f atf) := by
  intro i j
  apply Nat.le_induction
  · exact le_rfl
  · refine fun n hn hn' ↦ le_trans ?_ hn'
    if hnzero : n = 0 then
      exact hnzero ▸ le_top
    else
    simp only [function_wrapper]
    if hcond : function_wrapper f atf n = ⊥ then
      simp only [hcond, ↓reduceDIte, le_refl]
    else
    simp only [hcond, ↓reduceDIte]
    exact le_of_lt <| Nat.find_spec <| function_wrapper._proof_6 f atf n (of_eq_false (eq_false hcond))


lemma function_wrapper_prop3 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f): ∀ k : ℕ, function_wrapper f atf k ≤ f k := by
  intro k
  induction' k with k hk
  · simp only [function_wrapper, hf0, le_refl]
  · simp only [function_wrapper]
    if hcond : function_wrapper f atf k = ⊥ then
      simp only [hcond, ↓reduceDIte, bot_le]
    else
    simp only [hcond, ↓reduceDIte]
    rcases function_wrapper_prop0' f atf hfat hf0 (k+1) with ⟨jtilde,hjtilde⟩
    simp only [function_wrapper, ge_iff_le, hcond, ↓reduceDIte] at hjtilde
    if hjt : jtilde = k+1 then
      exact le_of_eq <| hjt ▸ hjtilde.2
    else
    exact hjtilde.2 ▸ (hfat <| le_of_lt <| lt_of_le_of_ne hjtilde.1 <| Ne.symm hjt)


lemma function_wrapper_prop5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f) : ∀ (i j : ℕ), i < j → j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) → function_wrapper f atf j < function_wrapper f atf i := by
  intro i
  have : ∀ j : ℕ, i+1 ≤ j → j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) → function_wrapper f atf j < function_wrapper f atf i := by
    apply Nat.le_induction
    · intro h
      simp only [function_wrapper]
      if hcond : function_wrapper f atf i = ⊥ then
        simp only [hcond, ↓reduceDIte, lt_self_iff_false]
        exact (Nat.find_min (function_wrapper_prop1 f atf hfat hf0) (Nat.lt_of_add_one_le h)) hcond
      else
      simp only [hcond, ↓reduceDIte]
      exact Nat.find_spec (function_wrapper._proof_6 f atf i (of_eq_false (eq_false hcond)))
    · intro j hij hind hj
      simp only [function_wrapper]
      if hcond : function_wrapper f atf j = ⊥ then
        simp only [hcond, ↓reduceDIte]
        apply bot_lt_iff_ne_bot.2
        by_contra!
        have := le_trans hj <| Nat.find_min' (function_wrapper_prop1 f atf hfat hf0) this
        linarith
      else
      simp only [hcond, ↓reduceDIte]
      if hcond' : j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) then
        exact lt_trans (Nat.find_spec (function_wrapper._proof_6 f atf j (of_eq_false (eq_false hcond)))) <| hind hcond'
      else
      by_contra!
      exact hcond <| le_bot_iff.1 <| (Nat.find_spec (function_wrapper_prop1 f atf hfat hf0)) ▸ function_wrapper_prop2 f atf (le_of_lt <| lt_of_not_le hcond')
  exact fun j hij hle ↦ this j hij hle


lemma function_wrapper_prop4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f) (k : ℕ) (hk : f k = ⊥) (htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N+1)) : (Nat.find <| function_wrapper_prop1 f atf hfat hf0) ≠ k := by
  let A := Nat.find <| function_wrapper_prop1 f atf hfat hf0
  let 𝒮 := {f t | (t ≤ k)}
  have helper : ∀ t : ℕ, ∃ l : ℕ, l ≤ k ∧ function_wrapper f atf t = f l := by
    intro t
    if hcond : function_wrapper f atf t = ⊥ then
      exact ⟨k,⟨le_rfl,hcond ▸ hk.symm⟩⟩
    else
    rcases function_wrapper_prop0' f atf hfat hf0 t with ⟨l,hl1,hl2⟩
    exact ⟨l,⟨byContradiction fun this ↦ hcond (le_bot_iff.mp (hk ▸ hfat (le_of_lt (Eq.mp (Mathlib.Tactic.PushNeg.not_le_eq l k) this))) ▸ hl2),hl2⟩⟩
  let Φ : Fin (A+1) → 𝒮 := fun d ↦ ⟨f (Nat.find (helper d)),Set.mem_setOf.mpr ⟨Nat.find (helper d),⟨(Nat.find_spec (helper d)).1,rfl⟩⟩⟩
  have hΦ : Function.Injective Φ := by
    intro d1 d2 h
    simp only [Subtype.mk.injEq, Φ, 𝒮] at h
    have := (Nat.find_spec (helper d2)).2.symm ▸ (Nat.find_spec (helper d1)).2.symm ▸ h
    if hd : d1 < d2 then
      exact False.elim <| (lt_self_iff_false (function_wrapper f atf ↑d2)).mp <| this ▸ function_wrapper_prop5 f hf0 atf hfat d1 d2 hd (Fin.is_le d2)
    else
      if hd' : d2 < d1 then
        exact False.elim <| (lt_self_iff_false (function_wrapper f atf ↑d2)).mp <| this ▸ function_wrapper_prop5 f hf0 atf hfat d2 d1 hd' (Fin.is_le d1)
      else
      exact Fin.le_antisymm (le_of_not_lt hd') (le_of_not_lt hd)
  let fS : Fin (k+1) → 𝒮 := fun n ↦ ⟨f n,Set.mem_setOf.mpr ⟨n,⟨Fin.is_le n,rfl⟩⟩⟩
  have fSsuj : Function.Surjective fS := by
    intro y
    rcases y.prop.out with ⟨n1,n2,n3⟩
    use ⟨n1,Nat.lt_succ_of_le n2⟩, SetCoe.ext n3
  have : Fintype 𝒮 :=  Set.Finite.fintype <| Finite.of_surjective fS fSsuj
  have ineq1: A + 1 ≤ Fintype.card ↑𝒮 := Fintype.card_fin (A+1) ▸ Fintype.card_le_of_injective Φ hΦ
  have ineq2 : Fintype.card ↑𝒮 < k + 1 := Fintype.card_fin (k+1) ▸ Fintype.card_lt_of_surjective_not_injective fS fSsuj <| Function.not_injective_iff.mpr ⟨⟨htech.choose,Nat.lt_add_right 1 htech.choose_spec.1⟩, ⟨htech.choose+1,Nat.add_lt_add_right htech.choose_spec.1 1⟩,⟨SetCoe.ext htech.choose_spec.2,by simp⟩⟩
  exact ne_of_lt <| Nat.succ_lt_succ_iff.mp <| lt_of_le_of_lt ineq1 ineq2


lemma function_wrapper_prop6 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f)
(P : {z : ℒ × ℒ // z.1 < z.2} → Prop)
(ho : ∀ i : ℕ, i < Nat.find atf → (hfi :f (i + 1) < f i) → P ⟨(f (i+1), f i),hfi⟩) : ∀ i : ℕ, (hi : i < Nat.find (function_wrapper_prop1 f atf hfat hf0)) → P ⟨(function_wrapper f atf (i + 1),function_wrapper f atf i), function_wrapper_prop5 f hf0 atf hfat i (i+1) (Nat.lt_succ_self i) (Nat.succ_le.2 hi)⟩ := by
  intro i hi
  simp only [function_wrapper]
  have hcond : function_wrapper f atf i ≠ ⊥ := by
    by_contra!
    have := Nat.find_min' (function_wrapper_prop1 f atf hfat hf0) this
    linarith
  simp only [hcond, ↓reduceDIte]
  rcases function_wrapper_prop0' f atf hfat hf0 i with ⟨j,⟨_,hj⟩⟩
  simp only [hj]
  rw [hj] at hcond
  have hcondnew : ∃ l : ℕ, f l < f j := by
    rcases atf with ⟨k,hk⟩
    use k
    rw [hk]
    (expose_names; exact Ne.bot_lt' (id (Ne.symm hcond_1)))
  let jtilde := Nat.find hcondnew
  expose_names
  have heq : Nat.find ((funext fun k ↦ congrArg (LT.lt (f k)) hj) ▸ function_wrapper._proof_6 f atf i (of_eq_false (eq_false hcond_1))) = (jtilde -1) +1:= by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
    by_contra!
    simp only [Nat.lt_one_iff, Nat.find_eq_zero] at this
    exact (not_lt_of_le le_top) <| hf0 ▸ this
  have ha : f j = f (jtilde -1) := by
    have : ∀ j' : ℕ, j ≤ j' → j' < jtilde → f j' = f j := by
      apply Nat.le_induction
      · exact fun _ ↦ rfl
      · intro n hn hn' hn''
        by_contra!
        have := lt_of_le_of_lt (Nat.find_min' hcondnew <| lt_of_le_of_ne (hfat (Nat.le_add_right_of_le hn)) this) hn''
        linarith
    refine Eq.symm <| this (jtilde -1) ?_ (by linarith)
    by_contra!
    exact (lt_self_iff_false (f j)).mp <| lt_of_le_of_lt (hfat (Nat.le_of_pred_lt this)) (Nat.find_spec hcondnew)
  conv =>
    arg 1; arg 1; arg 2;
    rw [ha]
  have yah : f jtilde < f (jtilde -1)  := lt_of_lt_of_eq (Nat.find_spec hcondnew) ha
  have : f (jtilde - 1 + 1) < f (jtilde - 1) := by
    conv_lhs =>
      arg 1;
      apply Nat.sub_one_add_one <| fun this ↦ (lt_self_iff_false ⊤).mp <| hf0 ▸ lt_of_lt_of_le (this ▸ yah) le_top
    exact yah
  have := ho (jtilde -1) (byContradiction fun this' ↦ not_le_of_gt (lt_of_le_of_lt bot_le yah) (Nat.find_spec atf ▸ hfat (le_of_not_lt this'))) this
  simp only [← heq] at this
  exact this

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

lemma μ_bot_JH_eq_μ_tot {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hsl : SlopeLike μ] (JH : JordanHolderFiltration μ) : ∀ i : ℕ, (hi : i < Nat.find JH.fin_len) → μ ⟨(⊥, JH.filtration i), by
  rw [← Nat.find_spec JH.fin_len]
  apply JH.strict_anti
  exact hi
  exact le_rfl
  ⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
  intro i hi
  induction' i with i hi'
  · simp only [JH.first_eq_top]
  · have := seesaw_useful μ hsl ⊥ (JH.filtration (i + 1)) ⊤ ⟨by
      rw [← Nat.find_spec JH.fin_len]
      apply JH.strict_anti
      exact hi
      exact le_rfl
      ,by
      rw [← JH.first_eq_top]
      apply JH.strict_anti
      exact Nat.zero_lt_succ i
      exact le_of_lt hi
      ⟩
    refine (this.2.2.2.2 ?_).1
    rw [← JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]
    if htop : JH.filtration i = ⊤ then
      simp only [htop]
    else
    have := seesaw_useful μ hsl (JH.filtration (i + 1)) (JH.filtration i) ⊤ ⟨by
      apply JH.strict_anti
      exact lt_add_one i
      exact Nat.le_of_succ_le hi
      ,Ne.lt_top' fun a ↦ htop (id (Eq.symm a))
      ⟩
    refine (this.2.2.2.1 ?_).1
    have hi' := hi' (Nat.lt_of_succ_lt hi)
    have := seesaw_useful μ hsl ⊥ (JH.filtration i) ⊤ ⟨by
      rw [← Nat.find_spec JH.fin_len]
      apply JH.strict_anti
      · exact Nat.lt_of_succ_lt hi
      · exact le_rfl
      ,Ne.lt_top' fun a ↦ htop (id (Eq.symm a))⟩
    rw [← (this.2.2.1 hi').2,JH.step_cond₁ i <| Nat.lt_of_succ_lt hi]

lemma semistable_of_step_cond₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N =⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) → Semistable (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
  intro h
  intro i hi
  have h := h i hi
  apply (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.2 (fun _ _ ↦ inferInstance)
  apply (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).1
  apply eq_of_le_of_le ?_ ?_
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
    have := ((seesaw_useful μ inferInstance (filtration (i + 1)) u.val (filtration i) ⟨(lt_of_le_of_ne u.prop.1 (by
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

lemma stable_of_step_cond₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N =⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i):
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩)
→ (
∀ i : ℕ, (hi : i < Nat.find fin_len) → Stable (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
    intro h
    intro i hi
    refine { toSemistable := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi, stable := ?_ }
    · intro x hx hx'
      have := (proposition_4_1 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance).1
      have this' := (proposition_4_1 (Resμ ⟨(filtration (i+1), x.val), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ μ) inferInstance inferInstance).1
      unfold μAstar at this
      unfold μAstar at this'
      simp only [μA_res_intvl,μmin_res_intvl] at *
      rw [this]
      have t1: @Bot.bot (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderBot.toBot = filtration (i + 1) := by rfl
      have t2 : @Top.top (Interval ⟨(filtration (i + 1), ↑x), lt_of_le_of_ne (Subtype.prop x).left fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc)))⟩) OrderTop.toTop = x.val := by rfl
      have t3 : (@Bot.bot (Interval ⟨(filtration (i + 1), ↑x), lt_of_le_of_ne (Subtype.prop x).left fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc)))⟩) OrderBot.toBot).val = filtration (i + 1) := by rfl
      simp only [t1,t2,t3] at *
      rw [this']
      have hss := semistable_of_step_cond₂ μ filtration fin_len strict_anti h i hi
      have := (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.1 hss
      have := (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).2 this
      simp only [μmin_res_intvl,μ_res_intvl] at this
      have t4 : @Bot.bot (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderBot.toBot = filtration (i+1) := by rfl
      have t5 : @Top.top (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderTop.toTop = filtration i := by rfl
      simp only [t4, t5] at *
      rw [this]
      apply ne_of_lt
      have : μmin μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ ≤ μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          exact hx <| Subtype.coe_inj.1 <| id (Eq.symm hc)
          ))⟩ := by
        apply sInf_le
        simp only [ne_eq, id_eq, Set.mem_setOf_eq]
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
          )) <| lt_iff_le_not_le.mpr (lt_top_iff_ne_top.2 hx')

lemma res_ss {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ]
[StrongDescendingChainCondition' μ] [Affine μ] (JH : JordanHolderFiltration μ) (h : JH.filtration (Nat.find JH.fin_len - 1) < ⊤) : Semistable (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ) := by
  apply (thm4d21 (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ) inferInstance inferInstance inferInstance).2.2 (fun _ _ ↦ inferInstance)
  apply (List.TFAE.out (thm4d21 (Resμ ⟨(JH.filtration (Nat.find JH.fin_len - 1),⊤),h⟩ μ) inferInstance inferInstance inferInstance).1 1 3).1
  rw [μmin_res_intvl, μ_res_intvl]
  simp only [μmin]
  apply eq_of_le_of_le ?_ ?_
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
    have := (List.TFAE.out (thm4d21 μ inferInstance inferInstance inferInstance).1 1 3).2 this
    have this' : μ ⟨(u,⊤),lt_top_iff_ne_top.2 hu1.2⟩ ≥ μ ⟨(⊥,⊤),bot_lt_top⟩ := by
      rw [← this]
      apply sInf_le
      use u, ⟨in_TotIntvl _,hu1.2⟩
    have := μ_bot_JH_eq_μ_tot JH (Nat.find JH.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JH)
    rw [((seesaw_useful μ inferInstance ⊥ (JH.filtration (Nat.find JH.fin_len - 1)) ⊤ ⟨by
      by_contra hc
      simp only [not_bot_lt_iff] at hc
      exact (Nat.find_min JH.fin_len <| Nat.sub_one_lt <| JH_pos_len JH) hc
      ,h⟩).2.2.1 this).2] at this'
    exact this'

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [iml : IsModularLattice ℒ]
{I : {p : ℒ × ℒ // p.1 < p.2}} : IsModularLattice (Interval I) where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    apply iml.sup_inf_le_assoc_of_le
    exact hxz


lemma looooooooooooooooog_lemma : ∀ n : ℕ, ∀ ℒ : Type*, ∀ _: Nontrivial ℒ, ∀ _ : Lattice ℒ, ∀ _ : BoundedOrder ℒ, ∀ _ : WellFoundedGT ℒ,
∀ _ : IsModularLattice ℒ,
∀ S : Type*, ∀ _ : CompleteLinearOrder S, ∀ μ : {p : ℒ × ℒ // p.1 < p.2} → S,
∀ _ : FiniteTotalPayoff μ, ∀ _ : SlopeLike μ,
∀ _ : Semistable μ, ∀ _ : StrongDescendingChainCondition' μ, ∀ _ : Affine μ, (∃ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≤ n) → (∀ JH' : JordanHolderFiltration μ, Nat.find JH'.fin_len ≤ n) := by
  intro n
  induction' n with n hn
  · intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hwdcc' affine ⟨JH,hJH⟩ JH'
    simp only [nonpos_iff_eq_zero, Nat.find_eq_zero, JH.first_eq_top, top_ne_bot] at hJH
  · intro ℒ ntl l bo wacc hmod S clo μ hftp hsl hst hwdcc' affine ⟨JHy,hJHy⟩ JHx
    if htriv : Nat.find JHx.fin_len = 1 then
      have := JHx.step_cond₂ 0 (Nat.lt_of_sub_eq_succ htriv)
      simp only [zero_add,← htriv,Nat.find_spec JHx.fin_len,JHx.first_eq_top] at this
      have : Nat.find JHy.fin_len = 1 := by
        have h : Nat.find JHy.fin_len ≠ 0 := by
          intro h'
          simp only [Nat.find_eq_zero, JHy.first_eq_top, top_ne_bot] at h'
        by_contra h'
        have this' := JHy.step_cond₁ (Nat.find JHy.fin_len - 1) (Nat.sub_one_lt h)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHy,Nat.find_spec JHy.fin_len] at this'
        exact (lt_irrefl _ <| this' ▸ this (JHy.filtration <| Nat.find JHy.fin_len - 1) (bot_lt_iff_ne_bot.2 <| Nat.find_min JHy.fin_len <| Nat.sub_one_lt <| JH_pos_len JHy) <| (JHy.first_eq_top) ▸ JHy.strict_anti 0 (Nat.find JHy.fin_len - 1) (by omega) (Nat.sub_le (Nat.find JHy.fin_len) 1)).elim
      rw [htriv]
      exact Nat.le_add_left 1 n
    else
    have : 0 < Nat.find JHx.fin_len - 1 := by
      have h : Nat.find JHx.fin_len ≠ 0 := by
        intro h'
        simp only [Nat.find_eq_zero, JHx.first_eq_top, top_ne_bot] at h'
      omega
    let Ires : {p : ℒ × ℒ // p.1 < p.2} := ⟨(JHx.filtration (Nat.find JHx.fin_len - 1),⊤),(JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)⟩
    have nt := (JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)
    have ftpLres : FiniteTotalPayoff (Resμ Ires μ) := by
      refine { fin_tot_payoff := ?_ }
      simp only [Resμ]
      have := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
      simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this
      exact ((seesaw_useful μ hsl ⊥ (JHx.filtration <| Nat.find JHx.fin_len - 1) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this).2 ▸ hftp.fin_tot_payoff
    let JH_raw : ℕ → (Interval Ires) := fun n ↦ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1)) ⊔ JHy.filtration n,⟨le_sup_left,le_top⟩⟩
    have JH_raw_antitone : Antitone JH_raw := by
      intro n1 n2 hn
      apply sup_le_sup_left <| JHy.antitone hn
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simp only [JH_raw,Resμ,JHy.first_eq_top, le_top, sup_of_le_right, JH_raw]
      rfl
    have JH_raw_fin_len: JH_raw (Nat.find JHy.fin_len) = ⊥ := by
      simp only [JH_raw, Nat.find_spec JHy.fin_len, bot_le, sup_of_le_left, JH_raw]
      rfl
    let JHfinal := function_wrapper JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simp only [JHfinal,function_wrapper]
    have hcond1 : ∀ i < Nat.find (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩: ∃ k, JH_raw k = ⊥), ∀ (hfi : JH_raw (i + 1) < JH_raw i), (fun z ↦ Resμ Ires μ z = Resμ Ires μ ⟨(⊥, ⊤), bot_lt_top⟩) ⟨(JH_raw (i + 1), JH_raw i), hfi⟩ := by
      intro j hj hfj
      simp only [Resμ,JH_raw]
      have htrans : μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1),⊤),(JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        have := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this
        exact ((seesaw_useful μ hsl ⊥ (JHx.filtration <| Nat.find JHx.fin_len - 1) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this).2.symm
      have hj': ∀ j: ℕ, j ≤ Nat.find JHy.fin_len → μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j), lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        refine fun j hj ↦ eq_of_le_of_le ?_ ?_
        · have : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
            exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
          rw [← this hst]
          apply le_sSup
          simp only [ne_eq, Set.mem_setOf_eq]
          use JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j, ⟨in_TotIntvl _,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
        · have : μmin μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ ≤ μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ := by
            apply sInf_le
            simp only [ne_eq, Set.mem_setOf_eq]
            use ⊥, ⟨⟨le_rfl, le_of_lt <| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
          refine le_trans ?_ this
          rw [μA_eq_μmin μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JHy.filtration j), lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx)))) le_sup_left⟩]
          if hjbot : ⊥ = JHy.filtration j  then
            simp only [← hjbot, bot_le, sup_of_le_left]
            rw [← μA_eq_μmin μ]
            have := JHx.step_cond₁ (Nat.find JHx.fin_len -1) (by omega)
            rw [← this]
            unfold μmin
            apply le_sInf
            intro b hb
            rcases hb with ⟨u,hu1,hu2⟩
            rw [← hu2]
            have := JHx.step_cond₂ (Nat.find JHx.fin_len -1) (by omega) u
            simp only [Nat.sub_one_add_one <| JH_pos_len JHx, Nat.find_spec JHx.fin_len] at *
            if ubot : u = ⊥ then
              simp only [ubot]
              exact le_rfl
            else
              apply bot_lt_iff_ne_bot.2 at ubot
              have := this ubot (lt_of_le_of_ne hu1.1.2 hu1.2)
              exact le_of_lt <| ((seesaw_useful μ hsl ⊥ u (JHx.filtration (Nat.find JHx.fin_len - 1)) ⟨ubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩).1.1 this).2
          else
          have := (proposition_2_8 μ inferInstance (JHx.filtration (Nat.find JHx.fin_len - 1)) (JHy.filtration j) ⊥ ⟨bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx))),bot_lt_iff_ne_bot.2 fun a ↦ hjbot (id (Eq.symm a))⟩).1
          convert this.le
          have t1 : μ TotIntvl = μA μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1)), bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx)))⟩ := by
            rw [← μA_eq_μmin μ]
            have hess := μ_bot_JH_eq_μ_tot JHx (Nat.find JHx.fin_len -1) (by omega)
            rw [← hess]
            unfold μmin
            refine eq_of_le_of_le ?_ ?_
            · apply le_sInf
              intro h hb
              simp only [ne_eq, id_eq, Set.mem_setOf_eq] at hb
              rcases hb with ⟨u,hu1,hu2⟩
              rw [← hu2]
              if hubot : u = ⊥ then
                simp only [hubot, le_refl]
              else
              by_contra hc
              simp only [not_le] at hc
              have := seesaw_useful μ hsl ⊥ u (JHx.filtration (Nat.find JHx.fin_len - 1)) ⟨bot_lt_iff_ne_bot.2 hubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩
              have hc := (this.2.1.2.2 hc).1
              rw [hess] at hc
              have := (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 hst)
              have this' : μ ⟨(⊥, u), bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μmax μ TotIntvl := by
                apply le_sSup
                simp only [ne_eq, Set.mem_setOf_eq]
                use u, ⟨in_TotIntvl _,Ne.symm hubot⟩
              rw [this] at this'
              exact (not_le_of_lt hc this').elim
            · apply sInf_le
              simp only [ne_eq, id_eq, Set.mem_setOf_eq]
              use ⊥
              simp only [exists_prop, and_true]
              refine ⟨⟨le_rfl,bot_le⟩, ?_⟩
              by_contra hc
              have := (Nat.find_spec JHx.fin_len) ▸ JHx.strict_anti (Nat.find JHx.fin_len -1) (Nat.find JHx.fin_len) (by omega) le_rfl
              rw [← hc] at this
              exact lt_irrefl _ this
          have t2 : μ TotIntvl = μA μ ⟨(⊥, JHy.filtration j), bot_lt_iff_ne_bot.2 fun a ↦ hjbot (id (Eq.symm a))⟩ := by
            rw [← μA_eq_μmin μ]
            have hess := μ_bot_JH_eq_μ_tot JHy j (by
              refine lt_of_le_of_ne hj ?_
              by_contra hc
              exact hjbot (hc ▸ Nat.find_spec JHy.fin_len).symm
            )
            rw [← hess]
            unfold μmin
            refine eq_of_le_of_le ?_ ?_
            · apply le_sInf
              intro h hb
              simp only [ne_eq, id_eq, Set.mem_setOf_eq] at hb
              rcases hb with ⟨u,hu1,hu2⟩
              rw [← hu2]
              if hubot : u = ⊥ then
                simp only [hubot, le_refl]
              else
              by_contra hc
              simp only [not_le] at hc
              have := seesaw_useful μ hsl ⊥ u (JHy.filtration j) ⟨bot_lt_iff_ne_bot.2 hubot,lt_of_le_of_ne hu1.1.2 hu1.2⟩
              have hc := (this.2.1.2.2 hc).1
              rw [hess] at hc
              have := (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 hst)
              have this' : μ ⟨(⊥, u), bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μmax μ TotIntvl := by
                apply le_sSup
                simp only [ne_eq, Set.mem_setOf_eq]
                use u, ⟨in_TotIntvl _,Ne.symm hubot⟩
              rw [this] at this'
              exact (not_le_of_lt hc this').elim
            · apply sInf_le
              simp only [ne_eq, id_eq, Set.mem_setOf_eq]
              use ⊥
              simp only [exists_prop, and_true]
              exact ⟨⟨le_rfl,bot_le⟩,hjbot⟩
          rw [← t1,← t2]
          exact Eq.symm (min_self (μ TotIntvl))
      have tj1 := hj' j (le_of_lt <| lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)
      have := tj1 ▸ ((seesaw_useful μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration (j+1)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j) ⟨lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left,lt_iff_le_not_le.mpr hfj⟩).2.2.1 <| tj1 ▸ hj' (j+1) (lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)).2
      rw [← this]
      exact id (Eq.symm htrans)
    let JH_FINAL : JordanHolderFiltration (Resμ Ires μ) := by
      refine { filtration := JHfinal, antitone := function_wrapper_prop2 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩), fin_len := function_wrapper_prop1 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone JH_raw_first_top, strict_anti := fun i j hij hj ↦ function_wrapper_prop5 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone i j hij hj, first_eq_top := by simp only [JHfinal_first_top], step_cond₁ := fun k1 hk1 ↦ function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun z ↦ (Resμ Ires μ) z = (Resμ Ires μ) ⟨(⊥,⊤),bot_lt_top⟩) hcond1 k1 hk1, step_cond₂ := ?_ }
      · refine fun i hi ↦ function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun w ↦ ∀ z : (Interval Ires), (hw : w.val.1 < z) → z < w.val.2 → (Resμ Ires μ) ⟨(w.val.1,z),hw⟩ < (Resμ Ires μ) w ) (fun j hj hfj w hw1 hw2 ↦ ((seesaw_useful μ hsl ↑(JH_raw (j + 1)) w ↑(JH_raw j) ⟨lt_iff_le_not_le.mpr hw1,lt_iff_le_not_le.mpr hw2⟩).1.2.2 ?_).1) i hi
        have := hcond1 j hj hfj; simp only [Resμ] at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        have this' := ((seesaw_useful μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this').2
        rw [this]
        have hproblem : JHy.filtration (j + 1) ≠ JHy.filtration j ⊓ ↑w := by
          by_contra hc
          simp only [JH_raw] at hw1
          have hw1 := lt_iff_le_not_le.mpr hw1
          simp only [JH_raw] at hw2
          have hw2 := lt_iff_le_not_le.mpr hw2
          have := @hmod.sup_inf_le_assoc_of_le (JHx.filtration (Nat.find JHx.fin_len - 1)) (JHy.filtration j) w.val (by
            apply le_of_lt <| lt_of_le_of_lt le_sup_left hw1
            )
          rw [← hc, inf_eq_right.2 <| le_of_lt hw2] at this
          exact (not_le_of_lt hw1) this
        have hnle : ¬ (JHy.filtration j ≤ w) := by
          by_contra hc
          simp only [JH_raw] at hw2
          refine (not_le_of_lt hw2) ?_
          apply sup_le_iff.2
          refine ⟨?_,hc⟩
          simp only [JH_raw] at hw1
          have hw1 : JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JHy.filtration (j + 1) < w.val := by
            exact lt_iff_le_not_le.mpr hw1
          apply le_of_lt <| lt_of_le_of_lt le_sup_left hw1
        have heqs : μ ⟨(↑w, ↑(JH_raw j)), lt_iff_le_not_le.mpr hw2⟩ = μ ⟨(JHy.filtration j ⊓ w,JHy.filtration j),inf_lt_left.2 hnle⟩ := by
          rw [affine.affine (JHy.filtration j) w.val hnle]
          have : ↑(JH_raw j) = JHy.filtration j ⊔ w.val := by
            simp only [JH_raw]
            apply eq_of_le_of_le ?_ ?_
            · simp only [JH_raw] at hw1
              have hw1 := lt_iff_le_not_le.mpr hw1
              have hw1 := sup_le_sup_right (le_of_lt hw1) (JHy.filtration j)
              have := left_eq_sup.2 <| JHy.antitone (Nat.le_add_right j 1)
              rw [sup_comm] at this
              rw [sup_assoc, ← this] at hw1
              nth_rw 2 [sup_comm] at hw1
              exact hw1
            · simp only [JH_raw] at hw2
              have hw2 := lt_iff_le_not_le.mpr hw2
              have hw2 := sup_le_sup_right (le_of_lt hw2) (JHy.filtration j)
              nth_rw 1 [sup_assoc,sup_comm] at hw2
              simp only [Nat.find_le_iff, forall_exists_index, and_imp, Nat.lt_find_iff, ne_eq,
                le_refl, sup_of_le_left, sup_le_iff, le_sup_right, true_and, ge_iff_le, JH_raw] at *
              exact hw2
          simp only [this]
        rw [heqs,((by rfl):μ ⟨(↑(⊥: Interval Ires), ↑(⊤: Interval Ires)), nt⟩ = μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1), ⊤), nt⟩),← this',← JHy.step_cond₁ j <| lt_of_lt_of_le hj <| Nat.find_le JH_raw_fin_len]
        have hlt : JHy.filtration (j+1) < JHy.filtration j ⊓ w := by
          refine lt_of_le_of_ne (le_inf (JHy.antitone <| Nat.le_add_right j 1) ?_) hproblem
          simp only [sup_comm, JH_raw] at hw1
          exact le_of_lt <| lt_of_le_of_lt (le_sup_left) <| lt_iff_le_not_le.mpr hw1
        refine ((seesaw_useful μ hsl (JHy.filtration (j+1)) (JHy.filtration j ⊓ w) (JHy.filtration j) ⟨hlt,inf_lt_left.2 hnle⟩).1.1 ?_).2
        exact JHy.step_cond₂ j (by
          have this' := Nat.find_min (Exists.intro (Nat.find JHy.fin_len) JH_raw_fin_len : ∃ k, JH_raw k = ⊥) hj
          unfold JH_raw at this'
          by_contra hcontra
          push_neg at hcontra
          have : JHy.filtration j = ⊥ := le_bot_iff.mp <| (Nat.find_spec JHy.fin_len) ▸ JHy.antitone hcontra
          rw [this] at this'
          simp only [bot_le, sup_of_le_left, JHfinal, JH_raw] at this'
          exact this' rfl
          ) (JHy.filtration j ⊓ w) hlt <| inf_lt_left.mpr hnle
    have ha : Nat.find JH_FINAL.fin_len < Nat.find JHy.fin_len := by
      have : JHfinal (Nat.find JHy.fin_len) = ⊥ := by
        simp only [JHfinal,function_wrapper]
        have : JH_raw (Nat.find JHy.fin_len) = ⊥ := by
          simp only [JH_raw, Nat.find_spec JHy.fin_len, bot_le, sup_of_le_left, JHfinal, JH_raw]
          rfl
        have hweird := eq_bot_iff.2 <| this ▸ function_wrapper_prop3 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len)
        exact hweird
      refine lt_of_le_of_ne (Nat.find_min' JH_FINAL.fin_len this) ?_
      · let i0 := Nat.findGreatest (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n) (Nat.find JHy.fin_len -1)
        refine function_wrapper_prop4 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len) JH_raw_fin_len ⟨i0,⟨Nat.add_le_of_le_sub (Nat.one_le_iff_ne_zero.mpr <| JH_pos_len JHy) <| Nat.findGreatest_le (Nat.find JHy.fin_len -1),?_⟩⟩
        · have := @Nat.findGreatest_spec 0 (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n) inferInstance (Nat.find JHy.fin_len -1) (zero_le _) (by simp only [JHy.first_eq_top,
          le_top, JHfinal, JH_raw])
          have h1 : JH_raw (i0 + 1) = JHy.filtration i0 := by
            refine eq_of_le_of_not_lt (sup_le this <| JHy.antitone (Nat.le_add_right i0 1)) <| fun hc ↦ ?_
            have : i0 ≤ Nat.find JHy.fin_len - 1 := Nat.findGreatest_le (Nat.find JHy.fin_len -1)
            have hsmall : JHy.filtration (i0 + 1) < ↑(JH_raw (i0 + 1)) := by
              refine lt_of_le_of_ne le_sup_right ?_
              · by_contra hcon
                have this' := right_eq_sup.1 hcon
                if hw : i0 + 1 ≤ Nat.find JHy.fin_len -1 then
                  exact @Nat.findGreatest_is_greatest (i0+1) (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n) inferInstance (Nat.find JHy.fin_len -1) (lt_add_one _) hw this'
                else
                  have : i0 + 1 = Nat.find JHy.fin_len := by
                    have : i0 + 1 ≤ Nat.find JHy.fin_len := (Eq.symm <| Nat.sub_one_add_one <| JH_pos_len JHy) ▸ add_le_add_right this 1
                    omega
                  simp only [this, Nat.find_spec JHy.fin_len, le_bot_iff] at this'
                  exact Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx) this'
            have otherwise := JHy.step_cond₂ i0 ((Nat.le_sub_one_iff_lt <| zero_lt_iff.2 <| JH_pos_len JHy).1 this) ↑(JH_raw (i0 + 1)) hsmall hc
            rw [JHy.step_cond₁ i0 <| lt_of_le_of_lt this <| Nat.sub_one_lt <| JH_pos_len JHy ] at otherwise
            refine (lt_iff_not_le.1 otherwise) ?_
            rw [← JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)]
            simp only [Nat.sub_one_add_one <| JH_pos_len JHx]
            have himp : ¬ JHx.filtration (Nat.find JHx.fin_len - 1) ≤ JHy.filtration (i0+1) := by
              if hw : i0 + 1 ≤ Nat.find JHy.fin_len -1 then
                exact Nat.findGreatest_is_greatest (lt_add_one _) hw
              else
                have : i0 + 1 = Nat.find JHy.fin_len := by
                  have : i0 + 1 ≤ Nat.find JHy.fin_len := (Eq.symm <| Nat.sub_one_add_one <| JH_pos_len JHy) ▸ add_le_add_right this 1
                  omega
                simp only [this, Nat.find_spec JHy.fin_len, le_bot_iff, ne_eq]
                exact Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx)
            rw [(affine.affine (JHx.filtration (Nat.find JHx.fin_len - 1)) (JHy.filtration (i0+1)) himp).symm]
            if hif : JHx.filtration (Nat.find JHx.fin_len) = JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1) then
              simp only [hif]
              exact le_rfl
            else
              have hh : JHx.filtration (Nat.find JHx.fin_len) < JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1) := by
                simp only [Nat.find_spec JHx.fin_len] at *
                exact Ne.bot_lt' hif
              have := le_of_lt <| JHx.step_cond₂ (Nat.find JHx.fin_len -1) (Nat.sub_one_lt <| JH_pos_len JHx) (JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1)) ((Nat.sub_one_add_one <| JH_pos_len JHx) ▸ hh) <| inf_lt_left.mpr himp
              simp only [Nat.sub_one_add_one <| JH_pos_len JHx] at this
              exact byContradiction fun hcc ↦  (lt_iff_not_le.1 <| ((seesaw_useful μ hsl (JHx.filtration (Nat.find JHx.fin_len)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊓ JHy.filtration (i0 + 1)) (JHx.filtration (Nat.find JHx.fin_len -1)) ⟨hh,inf_lt_left.mpr himp⟩).2.1.2.2 <| lt_of_not_le hcc).1) this
          exact Subtype.coe_inj.1 <| h1 ▸ (sup_eq_right.2 this)
    let JHfun : ℕ → Interval Ires := fun n ↦
      if hn : n ≤ Nat.find JHx.fin_len - 1 then
        ⟨JHx.filtration n,⟨JHx.antitone hn,le_top⟩⟩
      else
        ⊥
    have JHfun_fin_len : ∃ N : ℕ, JHfun N = ⊥ := by
        simp only [JHfun]
        use Nat.find JHx.fin_len
        simp only [lt_iff_not_le.1 <| Nat.sub_one_lt <| JH_pos_len JHx, ↓reduceDIte, JHfun]
    have JHfun_antitone : Antitone JHfun := by
        intro n1 n2 hn
        by_cases h3 : n2 ≤ Nat.find JHx.fin_len - 1
        · simp only [JHfun,le_trans hn h3,h3]
          simp only [↓reduceDIte, JHfun]
          exact JHx.antitone hn
        · simp only [h3, ↓reduceDIte, bot_le, JHfun]
    have hhard : Nat.find JHfun_fin_len = Nat.find JHx.fin_len - 1 := by
      have hgreat : Nat.find JHfun_fin_len ≤ Nat.find JHx.fin_len - 1 := by
        refine Nat.find_min' JHfun_fin_len ?_
        unfold JHfun
        simp only [le_refl, ↓reduceDIte, JHfun]
        rfl
      refine eq_of_le_of_not_lt hgreat fun hv ↦ ?_
      have hweired : JHx.filtration (Nat.find JHfun_fin_len) = JHx.filtration (Nat.find JHx.fin_len - 1)  := by
        have this' := Nat.find_spec JHfun_fin_len
        unfold JHfun at this'
        rw [dif_pos hgreat] at this'
        apply Subtype.coe_inj.2 at this'
        exact this'
      exact (lt_self_iff_false (JHx.filtration (Nat.find JHx.fin_len - 1))).1 <| hweired ▸ JHx.strict_anti (Nat.find JHfun_fin_len) (Nat.find JHx.fin_len - 1) hv <| Nat.sub_le (Nat.find JHx.fin_len) 1
    let JHres : JordanHolderFiltration (Resμ Ires μ) := by
      refine { filtration := JHfun, antitone := JHfun_antitone, fin_len := JHfun_fin_len, strict_anti := fun i j hij hj ↦ ?_, first_eq_top := ?_, step_cond₁ := ?_, step_cond₂ := ?_ }
      · simp only [JHfun,hhard ▸ hj,le_of_lt <| lt_of_lt_of_le hij (hhard ▸ hj),dif_pos]
        have := JHx.strict_anti i j hij (le_trans (hhard ▸ hj) <| le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        refine lt_iff_le_and_ne.mpr ⟨Subtype.coe_le_coe.1 <| le_of_lt this,fun hu ↦ ?_⟩
        apply Subtype.coe_inj.2 at hu
        simp only [JHfun] at hu
        exact (lt_self_iff_false (JHx.filtration i)).mp <| hu ▸ this
      · simp only [JHfun, zero_le, ↓reduceDIte, JHx.first_eq_top]
        rfl
      · intro k1 hk1
        simp only [Resμ, JHfun]
        have hk1 := hhard ▸ hk1
        have hk1' : k1 + 1 ≤ Nat.find JHx.fin_len - 1 := hk1
        simp only [hk1',le_of_lt hk1]
        simp only [↓reduceDIte, JHfun]
        have := JHx.step_cond₁ k1 <| Nat.lt_of_lt_pred hk1
        simp only [JHfun] at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JHx)
        simp only [Resμ,Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        have ntop : JHx.filtration (Nat.find JHx.fin_len - 1) < ⊤ := by
          have : Nat.find JHx.fin_len - 1 ≠ 0 := by
            by_contra t
            rw [t] at hk1
            exact Nat.not_succ_le_zero k1 hk1
          rw [← JHx.first_eq_top]
          exact JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) (by (expose_names; exact this_1)) (le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        exact this ▸ (((seesaw_useful μ) inferInstance ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx),ntop⟩).2.2.1 this').2
      · intro i hi z hz hz'
        simp only [Resμ]
        have htemp : JHx.filtration (i + 1) < z.val := by
          simp only [JHfun,Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi] at hz
          exact lt_iff_le_not_le.mpr hz
        have htemp2 : z < JHx.filtration i := by
          simp only [JHfun,le_of_lt <| hhard ▸ hi] at hz'; simp only [↓reduceDIte, JHfun] at hz'
          exact lt_iff_le_not_le.mpr hz'
        simp only [JHfun]; simp only [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi,
          ↓reduceDIte, le_of_lt <| hhard ▸ hi, gt_iff_lt, JHfun]
        exact JHx.step_cond₂ i (Nat.lt_of_lt_pred <| hhard ▸ hi) z htemp htemp2
    exact Nat.le_add_of_sub_le <| hhard ▸ hn (Interval Ires) inferInstance inferInstance inferInstance inferInstance inferInstance S clo (Resμ Ires μ) ftpLres inferInstance (res_ss _ _) inferInstance inferInstance ⟨JH_FINAL,Nat.le_of_lt_succ <| Nat.lt_of_lt_of_le ha hJHy⟩ JHres


end impl

end HarderNarasimhan
