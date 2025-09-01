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
open Classical

namespace HarderNarasimhan

namespace impl
noncomputable def JHFil {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc n ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}
    if h𝒮 : 𝒮.Nonempty then
      (hacc.wf.has_min 𝒮 h𝒮).choose
    else
      ⊥


lemma JHFil_anti_mono {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∀ k : ℕ, JHFil μ hμ hμsl hst hdc k > ⊥ → JHFil μ hμ hμsl hst hdc k > JHFil μ hμ hμsl hst hdc (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simp only [h]
    exact hk


lemma JHFil_prop₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1),JHFil μ hμ hμsl hst hdc k),JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
  intro k
  induction' k with k hk
  . intro hk'
    simp only [JHFil]
    by_cases this : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · simp only [this]
      have this' := (hacc.wf.has_min _ this).choose_spec.1.2.2
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ this).choose ⊤ ⟨(hacc.wf.has_min _ this).choose_spec.1.choose,(hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.1⟩) (by aesop)) (by aesop)).2.symm
    · simp only [this]; simp
  · intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this] at hk'; simp [*] at hk'
    have jh_kp1_ntop' : JHFil μ hμ hμsl hst hdc k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil,jh_kp1_ntop]
      exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
    have bot_jh_kp1_eq_ans := (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.2.2
    by_cases jh_kp2_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc (k + 1) ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
    · have stupid : μ ⟨(⊥, (hacc.wf.has_min _ jh_kp2_ntop).choose), (hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.1⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ := by
        rw [(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.2,← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop ]
        simp
      have hfinal : μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ = μ ⟨((hacc.wf.has_min _ jh_kp2_ntop).choose, JHFil μ hμ hμsl hst hdc (k + 1)), (hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.1⟩ := by
        refine (Or.resolve_left ((Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ jh_kp2_ntop).choose (JHFil μ hμ hμsl hst hdc (k + 1)) ⟨(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose,(hacc.wf.has_min _ jh_kp2_ntop).choose_spec.1.out.choose_spec.1⟩) (?_)) (?_)).2
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [stupid]; simp only [JHFil,jh_kp1_ntop]; simp
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [stupid]; simp only [JHFil,jh_kp1_ntop]; simp
      conv_lhs =>
        arg 1; arg 1; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]; simp
      simp at hfinal
      rw [← hfinal]
      simp only [JHFil,jh_kp1_ntop]; simp
      simp at bot_jh_kp1_eq_ans
      exact bot_jh_kp1_eq_ans
    · conv_lhs =>
        arg 1; arg 1; arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]; simp
      have this': μ ⟨(⊥, JHFil μ hμ hμsl hst hdc k), jh_kp1_ntop'⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
        by_cases hh : k = 0
        · simp only [hh,JHFil]
        · have : JHFil μ hμ hμsl hst hdc k = JHFil μ hμ hμsl hst hdc ((k-1)+1) := by
            simp [Nat.sub_one_add_one hh]
          simp only [this]
          have : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc (k-1) ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty := by
            by_contra hthis
            rw [this] at jh_kp1_ntop'
            simp only [JHFil,hthis] at jh_kp1_ntop'; simp at jh_kp1_ntop'
          simp only [JHFil,this]; simp
          have := (hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.2
          simp at this
          exact this
      simp only [← this']
      have : JHFil μ hμ hμsl hst hdc (k + 1) < JHFil μ hμ hμsl hst hdc k := by
        simp only [JHFil,jh_kp1_ntop]
        exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
      have this'' :  μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), hk'⟩ = μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), JHFil μ hμ hμsl hst hdc k), this⟩ := by
        rw [hk jh_kp1_ntop',← bot_jh_kp1_eq_ans]
        simp only [JHFil,jh_kp1_ntop]; simp
      exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst hdc (k + 1)) (JHFil μ hμ hμsl hst hdc k) ⟨hk',this⟩) (fun this_1 ↦ ne_of_lt (lt_trans this_1.left this_1.right) this'')) (fun this_1 ↦ ne_of_lt (gt_trans this_1.1 this_1.2) (Eq.symm this''))).1


lemma JHFil_fin_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∃ N : ℕ, JHFil μ hμ hμsl hst hdc N = ⊥ := by
  by_contra hc
  simp at hc
  rcases hdc (fun n => JHFil μ hμ hμsl hst hdc n) <| strictAnti_of_add_one_lt <| fun n _ ↦ JHFil_anti_mono μ hμ hμsl hst hdc n (bot_lt_iff_ne_bot.2 <| hc n) with ⟨N, hN⟩
  exact hμ.symm <| hN ▸ JHFil_prop₁ μ hμ hμsl hst hdc N (bot_lt_iff_ne_bot.2 <| hc N)


lemma JHFil_prop₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [hwdcc' : WeakDescendingChainCondition' μ]
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → ∀ z : ℒ, (h' : JHFil μ hμ hμsl hst hdc (k + 1) < z) → (h'' : z < JHFil μ hμ hμsl hst hdc k) →
  μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), z), h'⟩ < μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), JHFil μ hμ hμsl hst hdc k), JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ := by
  intro k hk z h' h''
  have this_new : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
    have : WeakAscendingChainCondition μ := {wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))}
    exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hμsl this inferInstance).1 0 3).2 ((impl.thm4d21 μ hμsl this inferInstance).2.1 a)
  have this_new := this_new hst
  simp [μmax, TotIntvl] at this_new
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
      simp at hfp1bot
      simp at this
      exact (ne_of_lt this) hfp1bot.symm
    apply Set.not_nonempty_iff_eq_empty.1 at this
    apply Set.eq_empty_iff_forall_not_mem.1 at this
    have := this z
    simp at this
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
        simp at hk
      rw [← (hacc.wf.has_min _ hne).choose_spec.1.out.2.2] at this
      simp only [JHFil,hne]; simp
      simp at this
      exact this
  · have h''' : μ ⟨(⊥, z), lt_of_le_of_lt bot_le h'⟩ < μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
      refine lt_of_le_of_ne this_q ?_
      by_contra!
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · have := (hacc.wf.has_min _ hne).choose_spec.2 z (by use lt_of_le_of_lt bot_le h')
        simp only [JHFil,hne] at h'
        simp at *
        exact this h'
      · refine hne ?_
        use z, lt_of_le_of_lt bot_le h'
    have h'''' : μ ⟨(⊥, ⊤), bot_lt_top⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · simp only [JHFil,hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp at *
        exact this.symm
      · simp only [JHFil,hne] at hfp1bot
        simp at hfp1bot
    exact (JHFil_prop₁ μ hμ hμsl hst hdc k hk ).symm ▸ lt_trans ((Or.resolve_right <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (JHFil μ hμ hμsl hst hdc (k + 1)) z ⟨bot_lt_iff_ne_bot.2 hfp1bot,h'⟩) (not_and_iff_not_or_not.2 <| Or.inl <| not_lt_of_lt <| h'''' ▸ h''')) (not_and_iff_not_or_not.2 <| Or.inl <| ne_of_gt <| h'''' ▸ h''')).2 h'''


lemma JH_pos_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} : ∀ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≠ 0 := by
  intro JH h
  simp [JH.first_eq_top] at h


noncomputable def function_wrapper {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : ℕ → ℒ := fun n ↦
  match n with
  | 0 => ⊤
  | t + 1 =>
    if hcond : function_wrapper f atf t = ⊥ then
      ⊥
    else
      f <| Nat.find (⟨atf.choose,atf.choose_spec.symm ▸ bot_lt_iff_ne_bot.2 hcond⟩: ∃ k : ℕ, f k < function_wrapper f atf t)


lemma function_wrapper_prop0 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∀ i : ℕ, ∃ j : ℕ, f i = function_wrapper f atf j := by
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
      simp only [function_wrapper,hj ▸ h]; simp
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


lemma function_wrapper_prop0' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∀ i : ℕ, ∃ j : ℕ, j ≥ i ∧ function_wrapper f atf i = f j:= by
  intro i
  induction' i with i hi
  · use 0
    simp only [function_wrapper]; simp [*]
  · simp only [function_wrapper]
    if hcond : function_wrapper f atf i = ⊥ then
      simp [hcond]
      rcases hi with ⟨t,ht⟩
      rw [hcond] at ht
      use t + 1
      simp [*]
      exact ht.2 ▸ (Eq.symm <| le_bot_iff.1 <| ht.2 ▸ hf (Nat.le_succ t))
    else
    simp [hcond]
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
    simp [*]

lemma function_wrapper_prop1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∃ N : ℕ, function_wrapper f atf N = ⊥ := by
  rcases (function_wrapper_prop0 f atf hf hf0 atf.choose) with ⟨N,hN⟩
  exact ⟨N, hN ▸ atf.choose_spec⟩

lemma function_wrapper_prop2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : Antitone (function_wrapper f atf) := by
  intro i j
  apply Nat.le_induction
  · exact le_rfl
  · refine fun n hn hn' ↦ le_trans ?_ hn'
    if hnzero : n = 0 then
      exact hnzero ▸ le_top
    else
    simp only [function_wrapper]
    if hcond : function_wrapper f atf n = ⊥ then
      simp [hcond]
    else
    simp [hcond]
    exact le_of_lt <| Nat.find_spec <| function_wrapper._proof_6 f atf n (of_eq_false (eq_false hcond))


lemma function_wrapper_prop3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f): ∀ k : ℕ, function_wrapper f atf k ≤ f k := by
  intro k
  induction' k with k hk
  · simp [hf0,function_wrapper]
  · simp only [function_wrapper]
    if hcond : function_wrapper f atf k = ⊥ then
      simp [hcond]
    else
    simp [hcond]
    rcases function_wrapper_prop0' f atf hfat hf0 (k+1) with ⟨jtilde,hjtilde⟩
    simp only [function_wrapper] at hjtilde; simp [hcond] at hjtilde
    if hjt : jtilde = k+1 then
      exact le_of_eq <| hjt ▸ hjtilde.2
    else
    exact hjtilde.2 ▸ (hfat <| le_of_lt <| lt_of_le_of_ne hjtilde.1 <| Ne.symm hjt)


lemma function_wrapper_prop5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f) : ∀ (i j : ℕ), i < j → j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) → function_wrapper f atf j < function_wrapper f atf i := by
  intro i
  have : ∀ j : ℕ, i+1 ≤ j → j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) → function_wrapper f atf j < function_wrapper f atf i := by
    apply Nat.le_induction
    · intro h
      simp only [function_wrapper]
      if hcond : function_wrapper f atf i = ⊥ then
        simp [hcond]
        exact (Nat.find_min (function_wrapper_prop1 f atf hfat hf0) (Nat.lt_of_add_one_le h)) hcond
      else
      simp [hcond]
      exact Nat.find_spec (function_wrapper._proof_6 f atf i (of_eq_false (eq_false hcond)))
    · intro j hij hind hj
      simp only [function_wrapper]
      if hcond : function_wrapper f atf j = ⊥ then
        simp [hcond]
        apply bot_lt_iff_ne_bot.2
        by_contra!
        have := le_trans hj <| Nat.find_min' (function_wrapper_prop1 f atf hfat hf0) this
        linarith
      else
      simp [hcond]
      if hcond' : j ≤ Nat.find (function_wrapper_prop1 f atf hfat hf0) then
        exact lt_trans (Nat.find_spec (function_wrapper._proof_6 f atf j (of_eq_false (eq_false hcond)))) <| hind hcond'
      else
      by_contra!
      exact hcond <| le_bot_iff.1 <| (Nat.find_spec (function_wrapper_prop1 f atf hfat hf0)) ▸ function_wrapper_prop2 f atf (le_of_lt <| lt_of_not_le hcond')
  exact fun j hij hle ↦ this j (by linarith) hle


lemma function_wrapper_prop4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f) (k : ℕ) (hk : f k = ⊥) (htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N+1)) : (Nat.find <| function_wrapper_prop1 f atf hfat hf0) ≠ k := by
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
    simp [Φ] at h
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


lemma function_wrapper_prop6 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f)
(P : {z : ℒ × ℒ // z.1 < z.2} → Prop)
(ho : ∀ i : ℕ, i < Nat.find atf → (hfi :f (i + 1) < f i) → P ⟨(f (i+1), f i),hfi⟩) : ∀ i : ℕ, (hi : i < Nat.find (function_wrapper_prop1 f atf hfat hf0)) → P ⟨(function_wrapper f atf (i + 1),function_wrapper f atf i), function_wrapper_prop5 f hf0 atf hfat i (i+1) (Nat.lt_succ_self i) (Nat.succ_le.2 hi)⟩ := by
  intro i hi
  simp only [function_wrapper]
  have hcond : function_wrapper f atf i ≠ ⊥ := by
    by_contra!
    have := Nat.find_min' (function_wrapper_prop1 f atf hfat hf0) this
    linarith
  simp [hcond]
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
    simp at this
    exact (not_lt_of_le le_top) <| hf0 ▸ this
  have ha : f j = f (jtilde -1) := by
    have : ∀ j' : ℕ, j ≤ j' → j' < jtilde → f j' = f j := by
      apply Nat.le_induction
      · exact fun _ ↦ rfl
      · intro n hn hn' hn''
        by_contra!
        have := lt_of_le_of_lt (Nat.find_min' hcondnew <| lt_of_le_of_ne (hfat (by linarith)) this) hn''
        linarith
    refine Eq.symm <| this (jtilde -1) ?_ (by linarith)
    by_contra!
    exact (lt_self_iff_false (f j)).mp <| lt_of_le_of_lt (hfat (by linarith)) (Nat.find_spec hcondnew)
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
  simp [← heq] at this
  exact this

lemma μA_eq_μmin {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
[SlopeLike μ] (I : {p : ℒ × ℒ // p.1 < p.2}) :
μmin μ I = μA μ I := by
  convert Eq.symm <| (proposition_4_1 (Resμ I μ) {wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))} inferInstance).1
  · unfold μmin
    congr
    ext x
    constructor
    · intro hx
      simp only [ne_eq, Set.mem_setOf_eq] at *
      rcases hx with ⟨u,⟨hu1,hu2⟩⟩
      use ⟨u,hu1.1⟩
      use ⟨in_TotIntvl _,fun hc ↦ hu1.right (Subtype.coe_inj.mpr hc)⟩
      exact hu2
    · intro hx
      simp only [ne_eq, Set.mem_setOf_eq] at *
      rcases hx with ⟨u,⟨hu1,hu2⟩⟩
      use u.val
      use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.mp hc)⟩
      exact hu2
  · unfold μA μAstar μA Resμ
    simp only [ne_eq]
    congr
    ext x
    constructor
    · intro hx
      simp only [Set.mem_setOf_eq] at *
      rcases hx with ⟨u,⟨hu1,hu2⟩⟩
      use ⟨u,hu1.1⟩
      use ⟨in_TotIntvl _,fun hc ↦ hu1.right (Subtype.coe_inj.mpr hc)⟩
      convert hu2
      unfold μmax
      congr
      ext y
      constructor
      · intro hy
        simp only [ne_eq, Set.mem_setOf_eq] at *
        rcases hy with ⟨a,ha1,ha2⟩
        use a
        use ⟨⟨ha1.1.1,a.prop.2⟩,fun hc ↦ ha1.right (Subtype.coe_inj.mp hc)⟩
      · intro hy
        simp only [ne_eq, Set.mem_setOf_eq] at *
        rcases hy with ⟨a,ha1,ha2⟩
        use ⟨a,⟨le_trans hu1.1.1 ha1.1.1,ha1.1.2⟩⟩
        use ⟨⟨ha1.1.1,le_top⟩,fun hc ↦ ha1.right (Subtype.coe_inj.mpr hc)⟩
    · intro hx
      simp only [Set.mem_setOf_eq] at *
      rcases hx with ⟨u,⟨hu1,hu2⟩⟩
      use u
      use ⟨hu1.1,fun hc ↦ hu1.right (Subtype.coe_inj.mp hc)⟩
      rw [← hu2]
      unfold μmax
      congr
      ext y
      constructor
      · intro hy
        simp only [ne_eq, Set.mem_setOf_eq] at *
        rcases hy with ⟨a,ha1,ha2⟩
        use ⟨a,⟨le_trans hu1.1.1 ha1.1.1,ha1.1.2⟩⟩
        use ⟨⟨ha1.1.1,le_top⟩,fun hc ↦ ha1.right (Subtype.coe_inj.mpr hc)⟩
      · intro hy
        simp only [ne_eq, Set.mem_setOf_eq] at *
        rcases hy with ⟨a,ha1,ha2⟩
        use a
        use ⟨⟨ha1.1.1,a.prop.2⟩,fun hc ↦ ha1.right (Subtype.coe_inj.mp hc)⟩

--set_option maxHeartbeats 0
lemma looooooooooooooooog_lemma : ∀ n : ℕ, ∀ ℒ : Type, ∀ ntl: Nontrivial ℒ, ∀ l : Lattice ℒ, ∀ bo : BoundedOrder ℒ, ∀ wacc : WellFoundedGT ℒ,
∀ S : Type, ∀ clo : CompleteLinearOrder S, ∀ μ : {p : ℒ × ℒ // p.1 < p.2} → S,
∀ hftp : FiniteTotalPayoff μ, ∀ hsl : SlopeLike μ,
∀ hst : Semistable μ, ∀ hwdcc' : WeakDescendingChainCondition' μ, ∀ affine : Affine μ, (∃ JH : JordanHolderFiltration μ, Nat.find JH.fin_len ≤ n) → (∀ JH' : JordanHolderFiltration μ, Nat.find JH'.fin_len ≤ n) := by
  intro n
  induction' n with n hn
  · intro ℒ ntl l bo wacc S clo μ hftp hsl hst hwdcc' affine ⟨JH,hJH⟩ JH'
    simp [JH.first_eq_top] at hJH
  · intro ℒ ntl l bo wacc S clo μ hftp hsl hst hwdcc' affine ⟨JHy,hJHy⟩ JHx
    if htriv : Nat.find JHx.fin_len = 1 then
      have := JHx.step_cond₂ 0 (by linarith)
      simp only [zero_add,← htriv,Nat.find_spec JHx.fin_len,JHx.first_eq_top] at this
      have : Nat.find JHy.fin_len = 1 := by
        have h : Nat.find JHy.fin_len ≠ 0 := by
          intro h'
          simp [JHy.first_eq_top] at h'
        by_contra h'
        have this' := JHy.step_cond₁ (Nat.find JHy.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHy,Nat.find_spec JHy.fin_len] at this'
        exact (lt_irrefl _ <| this' ▸ this (JHy.filtration <| Nat.find JHy.fin_len - 1) (bot_lt_iff_ne_bot.2 <| Nat.find_min JHy.fin_len <| Nat.sub_one_lt <| JH_pos_len JHy) <| (JHy.first_eq_top) ▸ JHy.strict_anti 0 (Nat.find JHy.fin_len - 1) (by omega) (Nat.sub_le (Nat.find JHy.fin_len) 1)).elim
      aesop
    else
    have : 0 < Nat.find JHx.fin_len - 1 := by
      have h : Nat.find JHx.fin_len ≠ 0 := by
        intro h'
        simp [JHx.first_eq_top] at h'
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
            have : WeakAscendingChainCondition μ := {wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))}
            exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl this inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl this inferInstance).2.1 a)
          have := this hst
          unfold TotIntvl at this
          rw [← this]
          apply le_sSup
          simp
          use JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j, ⟨in_TotIntvl _,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
        · have : μmin μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ ≤ μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ := by
            apply sInf_le
            simp
            use ⊥, ⟨⟨le_rfl, le_of_lt <| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
          refine le_trans ?_ this
          rw [μA_eq_μmin μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JHy.filtration j), lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx)))) le_sup_left⟩]
          if hjbot : ⊥ = JHy.filtration j  then
            simp only [← hjbot, bot_le, sup_of_le_left]
            rw [← μA_eq_μmin μ]


            sorry
          else
          have := (proposition_2_8 μ inferInstance (JHx.filtration (Nat.find JHx.fin_len - 1)) (JHy.filtration j) ⊥ ⟨bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx))),bot_lt_iff_ne_bot.2 fun a ↦ hjbot (id (Eq.symm a))⟩).1
          convert this.le
          have t1 : μ TotIntvl = μA μ ⟨(⊥, JHx.filtration (Nat.find JHx.fin_len - 1)), bot_lt_iff_ne_bot.mpr (Nat.find_min JHx.fin_len (Nat.sub_one_lt (JH_pos_len JHx)))⟩ := by
            rw [← μA_eq_μmin μ]

            sorry
          have t2 : μ TotIntvl = μA μ ⟨(⊥, JHy.filtration j), bot_lt_iff_ne_bot.2 fun a ↦ hjbot (id (Eq.symm a))⟩ := by
            rw [← μA_eq_μmin μ]
            sorry
          rw [← t1,← t2]
          exact Eq.symm (min_self (μ TotIntvl))
      have tj1 := hj' j (le_of_lt <| lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)
      have := tj1 ▸ ((seesaw_useful μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration (j+1)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j) ⟨lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left,lt_iff_le_not_le.mpr hfj⟩).2.2.1 <| tj1 ▸ hj' (j+1) (lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)).2
      rw [← this]
      exact id (Eq.symm htrans)
    let JH_FINAL : JordanHolderFiltration (Resμ Ires μ) := by
      refine { filtration := JHfinal, antitone := function_wrapper_prop2 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩), fin_len := function_wrapper_prop1 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone JH_raw_first_top, strict_anti := fun i j hij hj ↦ function_wrapper_prop5 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone i j hij hj, first_eq_top := by simp [*], step_cond₁ := fun k1 hk1 ↦ function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun z ↦ (Resμ Ires μ) z = (Resμ Ires μ) ⟨(⊥,⊤),bot_lt_top⟩) hcond1 k1 hk1, step_cond₂ := ?_ }
      · refine fun i hi ↦ function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun w ↦ ∀ z : (Interval Ires), (hw : w.val.1 < z) → z < w.val.2 → (Resμ Ires μ) ⟨(w.val.1,z),hw⟩ < (Resμ Ires μ) w ) (fun j hj hfj w hw1 hw2 ↦ ((seesaw_useful μ hsl ↑(JH_raw (j + 1)) w ↑(JH_raw j) ⟨lt_iff_le_not_le.mpr hw1,lt_iff_le_not_le.mpr hw2⟩).1.2.2 ?_).1) i hi
        have := hcond1 j hj hfj;simp [Resμ] at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        have this' := ((seesaw_useful μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this').2
        rw [this]
        have hproblem : JHy.filtration (j + 1) ≠ JHy.filtration j ⊓ ↑w := sorry
        have hnle : ¬ (JHy.filtration j ≤ w) := by
          by_contra!
          simp [JH_raw] at hw2
          sorry
        have heqs : μ ⟨(↑w, ↑(JH_raw j)), lt_iff_le_not_le.mpr hw2⟩ = μ ⟨(JHy.filtration j ⊓ w,JHy.filtration j),inf_lt_left.2 hnle⟩ := by
          sorry
        rw [heqs,((by rfl):μ ⟨(↑(⊥: Interval Ires), ↑(⊤: Interval Ires)), nt⟩ = μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1), ⊤), nt⟩),← this',← JHy.step_cond₁ j <| lt_of_lt_of_le hj <| Nat.find_le JH_raw_fin_len]
        have hlt : JHy.filtration (j+1) < JHy.filtration j ⊓ w := by
          refine lt_of_le_of_ne (le_inf (JHy.antitone <| Nat.le_add_right j 1) ?_) hproblem
          simp [JH_raw,sup_comm] at hw1
          exact le_of_lt <| lt_of_le_of_lt (le_sup_left) <| lt_iff_le_not_le.mpr hw1
        refine ((seesaw_useful μ hsl (JHy.filtration (j+1)) (JHy.filtration j ⊓ w) (JHy.filtration j) ⟨hlt,inf_lt_left.2 hnle⟩).1.1 ?_).2
        exact JHy.step_cond₂ j (by
          have this' := Nat.find_min (Exists.intro (Nat.find JHy.fin_len) JH_raw_fin_len : ∃ k, JH_raw k = ⊥) hj
          unfold JH_raw at this'
          by_contra hcontra
          push_neg at hcontra
          have : JHy.filtration j = ⊥ := le_bot_iff.mp <| (Nat.find_spec JHy.fin_len) ▸ JHy.antitone hcontra
          rw [this] at this'
          simp at this'
          exact this' rfl
          ) (JHy.filtration j ⊓ w) hlt <| inf_lt_left.mpr hnle
    have ha : Nat.find JH_FINAL.fin_len < Nat.find JHy.fin_len := by
      have : JHfinal (Nat.find JHy.fin_len) = ⊥ := by
        simp only [JHfinal,function_wrapper]
        have : JH_raw (Nat.find JHy.fin_len) = ⊥ := by
          simp only [JH_raw]
          simp [Nat.find_spec JHy.fin_len]
          rfl
        have hweird := eq_bot_iff.2 <| this ▸ function_wrapper_prop3 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len)
        exact hweird
      refine lt_of_le_of_ne (Nat.find_min' JH_FINAL.fin_len this) ?_
      · let i0 := Nat.findGreatest (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n) (Nat.find JHy.fin_len -1)
        refine function_wrapper_prop4 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len) JH_raw_fin_len ⟨i0,⟨Nat.add_le_of_le_sub (Nat.one_le_iff_ne_zero.mpr <| JH_pos_len JHy) <| Nat.findGreatest_le (Nat.find JHy.fin_len -1),?_⟩⟩
        · have := @Nat.findGreatest_spec 0 (fun n ↦ JHx.filtration (Nat.find JHx.fin_len -1) ≤ JHy.filtration n) inferInstance (Nat.find JHy.fin_len -1) (zero_le _) (by simp [JHy.first_eq_top])
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
                  simp [this,Nat.find_spec JHy.fin_len] at this'
                  exact Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx) this'
            have otherwise := JHy.step_cond₂ i0 ((Nat.le_sub_one_iff_lt <| zero_lt_iff.2 <| JH_pos_len JHy).1 this) ↑(JH_raw (i0 + 1)) hsmall hc
            rw [JHy.step_cond₁ i0 <| lt_of_le_of_lt this <| Nat.sub_one_lt <| JH_pos_len JHy ] at otherwise
            refine (lt_iff_not_le.1 otherwise) ?_
            rw [← JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)]
            simp [Nat.sub_one_add_one <| JH_pos_len JHx]
            have himp : ¬ JHx.filtration (Nat.find JHx.fin_len - 1) ≤ JHy.filtration (i0+1) := by
              if hw : i0 + 1 ≤ Nat.find JHy.fin_len -1 then
                exact Nat.findGreatest_is_greatest (lt_add_one _) hw
              else
                have : i0 + 1 = Nat.find JHy.fin_len := by
                  have : i0 + 1 ≤ Nat.find JHy.fin_len := (Eq.symm <| Nat.sub_one_add_one <| JH_pos_len JHy) ▸ add_le_add_right this 1
                  omega
                simp [this,Nat.find_spec JHy.fin_len]
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
              simp [Nat.sub_one_add_one <| JH_pos_len JHx] at this
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
        simp [lt_iff_not_le.1 <| Nat.sub_one_lt <| JH_pos_len JHx]
    have JHfun_antitone : Antitone JHfun := by
        intro n1 n2 hn
        by_cases h3 : n2 ≤ Nat.find JHx.fin_len - 1
        · simp only [JHfun,le_trans hn h3,h3]; simp
          exact JHx.antitone hn
        · simp [JHfun,h3]
    have hhard : Nat.find JHfun_fin_len = Nat.find JHx.fin_len - 1 := by
      have hgreat : Nat.find JHfun_fin_len ≤ Nat.find JHx.fin_len - 1 := by
        refine Nat.find_min' JHfun_fin_len ?_
        unfold JHfun
        simp
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
        simp at hu
        exact (lt_self_iff_false (JHx.filtration i)).mp <| hu ▸ this
      · simp only [JHfun]; simp [JHx.first_eq_top]
        rfl
      · intro k1 hk1
        simp [Resμ]; simp only [JHfun]
        have hk1 := hhard ▸ hk1
        have hk1' : k1 + 1 ≤ Nat.find JHx.fin_len - 1 := hk1
        simp only [hk1',le_of_lt hk1]; simp
        have := JHx.step_cond₁ k1 <| Nat.lt_of_lt_pred hk1
        simp at this
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JHx)
        simp only [Resμ,Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this'
        have ntop : JHx.filtration (Nat.find JHx.fin_len - 1) < ⊤ := by
          have : Nat.find JHx.fin_len - 1 ≠ 0 := by
            by_contra t
            rw [t] at hk1
            linarith
          rw [← JHx.first_eq_top]
          exact JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) (by linarith) (le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        exact this ▸ (((seesaw_useful μ) inferInstance ⊥ (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx),ntop⟩).2.2.1 this').2
      · intro i hi z hz hz'
        simp only [Resμ]
        have htemp : JHx.filtration (i + 1) < z.val := by
          simp only [JHfun,Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi] at hz
          exact lt_iff_le_not_le.mpr hz
        have htemp2 : z < JHx.filtration i := by
          simp only [JHfun,le_of_lt <| hhard ▸ hi] at hz'; simp at hz'
          exact lt_iff_le_not_le.mpr hz'
        simp only [JHfun]; simp [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi,le_of_lt <| hhard ▸ hi]
        exact JHx.step_cond₂ i (Nat.lt_of_lt_pred <| hhard ▸ hi) z htemp htemp2
    exact Nat.le_add_of_sub_le <| hhard ▸ hn (Interval Ires) inferInstance inferInstance inferInstance inferInstance S clo (Resμ Ires μ) ftpLres inferInstance sorry inferInstance inferInstance ⟨JH_FINAL,Nat.le_of_lt_succ <| Nat.lt_of_lt_of_le ha hJHy⟩ JHres


end impl

end HarderNarasimhan
