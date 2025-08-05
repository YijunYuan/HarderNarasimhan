import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl
import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
import HarderNarasimhan.JordanHolderFiltration.Defs
import HarderNarasimhan.SlopeLike.Result
import Mathlib.Data.Finite.Card
open Classical

namespace HardarNarasimhan

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
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∀ k : ℕ,  (hk : JHFil μ hμ hμsl hst hdc k > ⊥) → ∀ z : ℒ, (h' : JHFil μ hμ hμsl hst hdc (k + 1) < z) → (h'' : z < JHFil μ hμ hμsl hst hdc k) →
  μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), z), h'⟩ < μ ⟨(JHFil μ hμ hμsl hst hdc (k + 1), JHFil μ hμ hμsl hst hdc k), JHFil_anti_mono μ hμ hμsl hst hdc k hk⟩ := by
  intro k hk z h' h''
  have this_new := (List.TFAE.out (impl.thm4d21 μ hμsl {wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))} {wdcc :=(fun f saf ↦ Exists.casesOn (hdc f saf) fun N hN ↦ Exists.intro N (Eq.symm hN ▸ le_top))}) 0 4).2 hst
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
        simp at h'
        simp at this
        exact this h'
      · refine hne ?_
        use z, lt_of_le_of_lt bot_le h'
    have h'''' : μ ⟨(⊥, ⊤), bot_lt_top⟩ = μ ⟨(⊥, JHFil μ hμ hμsl hst hdc (k + 1)), bot_lt_iff_ne_bot.2 hfp1bot⟩ := by
      by_cases hne : {p | ∃ (h : ⊥ < p), p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥, p), h⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩}.Nonempty
      · simp only [JHFil,hne]
        have := (hacc.wf.has_min _ hne).choose_spec.1.out.choose_spec.2
        simp at this
        simp
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
  · use 0
    simp only [function_wrapper]
    exact hf0
  · rcases hi with ⟨j,hj⟩
    if h : f i = ⊥ then
      use j
      rw [← hj,h]
      exact le_bot_iff.1 <| h ▸ hf (Nat.le_succ i)
    else
    if h' : f i = f (i+1) then
      use j
      exact h' ▸ hj
    else
      use j+1
      simp only [function_wrapper,hj ▸ h]
      simp
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
    simp only [function_wrapper]
    simp [*]
  · simp only [function_wrapper]
    if hcond : function_wrapper f atf i = ⊥ then
      simp [hcond]
      rcases hi with ⟨t,ht⟩
      rw [hcond] at ht
      use t + 1
      simp [*]
      rw [← ht.2]
      exact Eq.symm <| le_bot_iff.1 <| ht.2 ▸ hf (Nat.le_succ t)
    else
    simp [hcond]
    have hq := function_wrapper._proof_6 f atf i (of_eq_false (eq_false hcond))
    rcases hi with ⟨t,ht⟩
    rw [ht.2] at hq
    use Nat.find hq
    constructor
    · have := Nat.find_spec hq
      have : Nat.find hq > t := by
        by_contra d
        apply le_of_not_lt at d
        if hy: Nat.find hq = t then
          rw [hy] at this
          exact (lt_self_iff_false (f t)).1 this
        else
        exact (lt_self_iff_false (f <| Nat.find hq)).1 <| lt_of_lt_of_le this <| hf <| le_of_lt <| lt_of_le_of_ne d hy
      linarith
    simp [*]

lemma function_wrapper_prop1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf: Antitone f) (hf0 : f 0 = ⊤): ∃ N : ℕ, function_wrapper f atf N = ⊥ := by
  rcases (function_wrapper_prop0 f atf hf hf0 atf.choose) with ⟨N,hN⟩
  use N
  exact hN ▸ atf.choose_spec

lemma function_wrapper_prop2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) : Antitone (function_wrapper f atf) := by
  intro i j
  apply Nat.le_induction
  · exact le_rfl
  · refine fun n hn hn' ↦ le_trans ?_ hn'
    if hnzero : n = 0 then
      rw [hnzero]
      simp only [function_wrapper]
      exact le_top
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
    simp only [function_wrapper] at hjtilde
    simp [hcond] at hjtilde
    if hjt : jtilde = k+1 then
      rw [hjt] at hjtilde
      exact le_of_eq hjtilde.2
    else
    rw [hjtilde.2]
    exact hfat <| le_of_lt <| lt_of_le_of_ne hjtilde.1 <| Ne.symm hjt


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
      apply lt_of_not_le at hcond'
      exact hcond <| le_bot_iff.1 <| (Nat.find_spec (function_wrapper_prop1 f atf hfat hf0)) ▸ function_wrapper_prop2 f atf (le_of_lt hcond')
  exact fun j hij hle ↦ this j (by linarith) hle


lemma function_wrapper_prop4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (f : ℕ → ℒ) (hf0 : f 0 = ⊤) (atf : ∃ k, f k = ⊥) (hfat: Antitone f) (k : ℕ) (hk : f k = ⊥) (htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N+1)) : (Nat.find <| function_wrapper_prop1 f atf hfat hf0) ≠ k := by
  have Acond := function_wrapper_prop1 f atf hfat hf0
  let A := Nat.find Acond
  have shit := le_bot_iff.1 <| hk ▸ function_wrapper_prop3 f hf0 atf hfat k
  let 𝒮 := {f t | (t ≤ k)}
  have helper : ∀ t : ℕ, ∃ l : ℕ, l ≤ k ∧ function_wrapper f atf t = f l := by
    intro t
    if hcond : function_wrapper f atf t = ⊥ then
      use k
      simp
      rw [hcond]
      exact hk.symm
    else
    rcases function_wrapper_prop0' f atf hfat hf0 t with ⟨l,hl1,hl2⟩
    use l
    refine ⟨?_,hl2⟩
    by_contra!
    exact hcond <| (le_bot_iff.1 <| hk ▸ (hfat <| le_of_lt this)) ▸ hl2
  let Φ : Fin (A+1) → 𝒮 := by
    intro d
    use  f (Nat.find (helper d))
    refine Set.mem_setOf.mpr ?_
    use Nat.find (helper d)
    exact ⟨(Nat.find_spec (helper d)).1,rfl⟩
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
  let fS : Fin (k+1) → 𝒮 := by
    intro n
    use f n
    refine Set.mem_setOf.mpr ?_
    use n
    simp
    exact Fin.is_le n
  have fSsuj : Function.Surjective fS := by
    intro y
    rcases y.prop.out with ⟨n1,n2,n3⟩
    use ⟨n1,Nat.lt_succ_of_le n2⟩
    simp only [fS]
    exact SetCoe.ext n3
  have finS : Fintype 𝒮 :=  Set.Finite.fintype <| Finite.of_surjective fS fSsuj
  have ineq1: A + 1 ≤ Fintype.card ↑𝒮 := by
    have := Fintype.card_le_of_injective Φ hΦ
    simp at this
    exact this
  have hnot : ¬ Function.Injective fS := by
    rcases htech with ⟨N, hN1, hN2⟩
    refine Function.not_injective_iff.mpr ?_
    use ⟨N,by linarith⟩, ⟨N+1,by linarith⟩
    constructor
    · simp only [fS]
      exact SetCoe.ext hN2
    · simp
  have ineq2 : Fintype.card ↑𝒮 < k + 1 := by
    have := Fintype.card_lt_of_surjective_not_injective fS fSsuj hnot
    simp at this
    exact this
  have := lt_of_le_of_lt ineq1 ineq2
  simp at this
  apply ne_of_lt at this
  exact this


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
  have hjeff : j < Nat.find atf := by
    by_contra!
    exact hcond (le_bot_iff.1 <| Nat.find_spec atf ▸ hfat this)
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
  have hq : jtilde - 1 < Nat.find atf := by
    by_contra this'
    apply le_of_not_lt at this'
    exact (not_le_of_gt <| lt_of_le_of_lt bot_le yah) ((Nat.find_spec atf) ▸ hfat this')
  have : f (jtilde - 1 + 1) < f (jtilde - 1) := by
    conv_lhs =>
      arg 1;
      apply Nat.sub_one_add_one <| fun this ↦ (lt_self_iff_false ⊤).mp <| hf0 ▸ lt_of_lt_of_le (this ▸ yah) le_top
    exact yah
  have := ho (jtilde -1) hq this
  simp [← heq] at this
  exact this


lemma strange' : ∀ n : ℕ, ∀ ℒ : Type, ∀ ntl: Nontrivial ℒ, ∀ l : Lattice ℒ, ∀ bo : BoundedOrder ℒ, ∀ wacc : WellFoundedGT ℒ,
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
        have := this (JHy.filtration <| Nat.find JHy.fin_len - 1) (bot_lt_iff_ne_bot.2 <| Nat.find_min JHy.fin_len <| Nat.sub_one_lt <| JH_pos_len JHy) <| (JHy.first_eq_top) ▸ JHy.strict_anti 0 (Nat.find JHy.fin_len - 1) (by omega) (Nat.sub_le (Nat.find JHy.fin_len) 1)
        have this' := JHy.step_cond₁ (Nat.find JHy.fin_len - 1) (by omega)
        simp only [Nat.sub_one_add_one <| JH_pos_len JHy,Nat.find_spec JHy.fin_len] at this'
        rw [this'] at this
        exact (lt_irrefl _ this).elim
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
      apply sup_le_sup_left
      exact JHy.antitone hn
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simp only [JH_raw,Resμ]
      simp [JHy.first_eq_top]
      rfl
    have JH_raw_fin_len: JH_raw (Nat.find JHy.fin_len) = ⊥ := by
      simp only [JH_raw]
      simp [Nat.find_spec JHy.fin_len]
      rfl
    let JHfinal := function_wrapper JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simp only [JHfinal,function_wrapper]
    have JHfinal_fin_len : ∃ N : ℕ, JHfinal N = ⊥ := by
        exact function_wrapper_prop1 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone JH_raw_first_top
    let JH_FINAL : JordanHolderFiltration (Resμ Ires μ) := by
      refine { filtration := JHfinal, antitone := ?_, fin_len := ?_, strict_anti := ?_, first_eq_top := ?_, step_cond₁ := ?_, step_cond₂ := ?_ }
      · exact function_wrapper_prop2 JH_raw (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩)
      · exact JHfinal_fin_len
      · intro i j hij hj
        simp only [JHfinal]
        exact function_wrapper_prop5 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone i j hij hj
      · simp [*]
      · intro k1 hk1
        refine function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun z ↦ (Resμ Ires μ) z = (Resμ Ires μ) ⟨(⊥,⊤),bot_lt_top⟩) ?_ k1 hk1
        intro j hj hfj
        simp only [Resμ,JH_raw]
        have htrans : μ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1),⊤),(JHx.first_eq_top) ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
          have := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (by omega)
          simp only [Nat.sub_one_add_one <| JH_pos_len JHx,Nat.find_spec JHx.fin_len] at this
          refine ((seesaw_useful μ hsl ⊥ (JHx.filtration <| Nat.find JHx.fin_len - 1) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx,nt⟩).2.2.1 this).2.symm
        have hj': ∀ j: ℕ, j ≤ Nat.find JHy.fin_len → μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j), lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩ := by
          intro j hj
          refine eq_of_le_of_le ?_ ?_
          · have := (List.TFAE.out (thm4d21 μ hsl {wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))} inferInstance) 0 4).2 hst
            unfold TotIntvl at this
            rw [← this]
            simp only [μmax]
            apply le_sSup
            simp
            use JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j, ⟨in_TotIntvl _,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
          · have : μmin μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ ≤ μ ⟨(⊥,JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j),lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩ := by
              simp only [μmin]
              apply sInf_le
              simp
              use ⊥, ⟨⟨le_rfl, le_of_lt <| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩,Ne.symm <| bot_lt_iff_ne_bot.1<| lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left⟩
            refine le_trans ?_ this
            sorry
        have tj1 := hj' j (le_of_lt <| lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)
        have tj2 := hj' (j+1) (lt_of_lt_of_le hj <| Nat.find_min' ((⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) : ∃ k, JH_raw k = ⊥) JH_raw_fin_len)
        rw [← tj1] at tj2
        have := tj1 ▸ ((seesaw_useful μ hsl ⊥ (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration (j+1)) (JHx.filtration (Nat.find JHx.fin_len -1) ⊔ JHy.filtration j) ⟨lt_of_lt_of_le (bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len <| Nat.sub_one_lt <| JH_pos_len JHx) le_sup_left,lt_iff_le_not_le.mpr hfj⟩).2.2.1 tj2).2
        rw [← this]
        exact id (Eq.symm htrans)
      · intro i hi
        refine function_wrapper_prop6 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (fun w ↦ ∀ z : (Interval Ires), (hw : w.val.1 < z) → z < w.val.2 → (Resμ Ires μ) ⟨(w.val.1,z),hw⟩ < (Resμ Ires μ) w ) ?_ i hi
        intro j hj hfj z hz1 hz2
        simp only [Resμ,JH_raw]

        sorry
    have ha : Nat.find JH_FINAL.fin_len < Nat.find JHy.fin_len := by
      have : JHfinal (Nat.find JHy.fin_len) = ⊥ := by
        simp only [JHfinal,function_wrapper]
        have : JH_raw (Nat.find JHy.fin_len) = ⊥ := by
          simp only [JH_raw]
          simp [Nat.find_spec JHy.fin_len]
          rfl
        have hweird := eq_bot_iff.2 <| this ▸ function_wrapper_prop3 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len)
        exact hweird
      refine lt_of_le_of_ne ?_ ?_
      · exact Nat.find_min' JH_FINAL.fin_len this
      · refine function_wrapper_prop4 JH_raw JH_raw_first_top (⟨Nat.find JHy.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JHy.fin_len) JH_raw_fin_len ?_
        sorry
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
        · simp only [JHfun,le_trans hn h3,h3]
          simp
          exact JHx.antitone hn
        · simp [JHfun,h3]
    have hhard : Nat.find JHfun_fin_len = Nat.find JHx.fin_len - 1 := by
      have hgreat : Nat.find JHfun_fin_len ≤ Nat.find JHx.fin_len - 1 := by
        have : JHfun (Nat.find JHx.fin_len - 1) = ⊥ := by
          unfold JHfun
          simp
          rfl
        exact Nat.find_min' JHfun_fin_len this
      refine eq_of_le_of_not_lt hgreat ?_
      by_contra hv
      have : JHx.filtration (Nat.find JHx.fin_len - 1) < JHx.filtration (Nat.find JHfun_fin_len) := JHx.strict_anti (Nat.find JHfun_fin_len) (Nat.find JHx.fin_len - 1) hv <| Nat.sub_le (Nat.find JHx.fin_len) 1
      have this': JHfun (Nat.find JHfun_fin_len) = ⊥ := Nat.find_spec JHfun_fin_len
      have hweired : JHx.filtration (Nat.find JHfun_fin_len) = JHx.filtration (Nat.find JHx.fin_len - 1)  := by
        unfold JHfun at this'
        rw [dif_pos hgreat] at this'
        apply Subtype.coe_inj.2 at this'
        have bitch : ↑(⊥ : (Interval Ires)) = (JHx.filtration (Nat.find JHx.fin_len - 1)) := rfl
        rw [bitch] at this'
        simp only [← this']
      have := hweired ▸ this
      exact (lt_self_iff_false (JHx.filtration (Nat.find JHx.fin_len - 1))).1 this
    let JHres : JordanHolderFiltration (Resμ Ires μ) := by
      refine { filtration := ?_, antitone := ?_, fin_len := ?_, strict_anti := ?_, first_eq_top := ?_, step_cond₁ := ?_, step_cond₂ := ?_ }
      · use JHfun
      · exact JHfun_antitone
      · exact JHfun_fin_len
      · intro i j hij hj
        simp only [JHfun,hhard ▸ hj,le_of_lt <| lt_of_lt_of_le hij (hhard ▸ hj),dif_pos]
        have := JHx.strict_anti i j hij (le_trans (hhard ▸ hj) <| le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        refine lt_iff_le_and_ne.mpr ?_
        constructor
        · apply Subtype.coe_le_coe.1
          exact le_of_lt this
        · by_contra hu
          apply Subtype.coe_inj.2 at hu
          simp at hu
          exact (lt_self_iff_false (JHx.filtration i)).mp <| hu ▸ this
      · simp only [JHfun]
        simp [JHx.first_eq_top]
        rfl
      · intro k1 hk1
        simp [Resμ]
        simp only [JHfun]
        have hk1 := hhard ▸ hk1
        have hk1' : k1 + 1 ≤ Nat.find JHx.fin_len - 1 := hk1
        have hk1'' : k1 ≤ Nat.find JHx.fin_len - 1 := le_of_lt hk1
        simp only [hk1',le_of_lt hk1]
        simp
        have := JHx.step_cond₁ k1 <| Nat.lt_of_lt_pred hk1
        simp at this
        rw [this]
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (Nat.sub_one_lt <| JH_pos_len JHx)
        simp only [Resμ,Nat.sub_one_add_one <| JH_pos_len JHx] at this'
        simp only [Nat.find_spec JHx.fin_len] at this'
        have ntop : JHx.filtration (Nat.find JHx.fin_len - 1) < ⊤ := by
          have : Nat.find JHx.fin_len - 1 ≠ 0 := by
            by_contra t
            rw [t] at hk1
            linarith
          rw [← JHx.first_eq_top]
          exact JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) (by linarith) (le_of_lt <| Nat.sub_one_lt <| JH_pos_len JHx)
        exact (((seesaw_useful μ) inferInstance ⊥
          (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len (Nat.sub_one_lt <| JH_pos_len JHx),ntop⟩).2.2.1 this').2
      · intro i hi z hz hz'
        simp only [Resμ]
        have ilt : i < Nat.find JHx.fin_len := by
          rw [hhard] at hi
          exact Nat.lt_of_lt_pred hi
        have htemp : JHx.filtration (i + 1) < z.val := by
          simp only [JHfun] at hz
          simp [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi] at hz
          exact lt_iff_le_not_le.mpr hz
        have htemp2 : z < JHx.filtration i := by
          simp only [JHfun,le_of_lt <| hhard ▸ hi] at hz'
          simp at hz'
          exact lt_iff_le_not_le.mpr hz'
        have hnew := JHx.step_cond₂ i ilt z htemp htemp2
        simp [Resμ] at hnew
        simp only [JHfun]
        simp [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi,le_of_lt <| hhard ▸ hi]
        exact hnew
    have hn' := hn (Interval Ires) inferInstance inferInstance inferInstance inferInstance S clo (Resμ Ires μ) ftpLres inferInstance sorry inferInstance inferInstance ⟨JH_FINAL,Nat.le_of_lt_succ <| Nat.lt_of_lt_of_le ha hJHy⟩ JHres
    rw [hhard] at hn'
    exact Nat.le_add_of_sub_le hn'


end impl

end HardarNarasimhan
