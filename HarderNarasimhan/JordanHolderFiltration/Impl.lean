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


lemma strange {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ] [hwdcc' : WeakDescendingChainCondition' μ] [Affine μ] :
∀ k : ℕ, ∀ x : ℒ, (hx : x < ⊤) → (∃ JHx : JordanHolderFiltration (Resμ ⟨(x,⊤),hx⟩ μ), Nat.find JHx.fin_len = k) → (∀ JH : JordanHolderFiltration (Resμ ⟨(x,⊤),hx⟩ μ), k ≤ Nat.find JH.fin_len) := by
  intro k
  induction' k with k hk
  · rintro x hx ⟨JHx,hJHx⟩ JH
    have := JHx.first_eq_top ▸ hJHx ▸ Nat.find_spec JHx.fin_len
    exact False.elim <| bot_ne_top this.symm
  · intro x hx ⟨JHx,hJHx⟩ JH
    have h1: Nat.find JHx.fin_len ≠ 0 := fun h ↦ bot_ne_top (JHx.first_eq_top ▸ h ▸ Nat.find_spec JHx.fin_len).symm
    if kzero : k = 0 then
      rw [kzero,zero_add]
      refine Nat.one_le_iff_ne_zero.mpr <| fun h ↦ bot_ne_top (JH.first_eq_top ▸ h ▸ Nat.find_spec JH.fin_len).symm
    else
    if hnz : (JHx.filtration (Nat.find JHx.fin_len - 1)).val = ⊤ then
      have : 0 < Nat.find JHx.fin_len - 1 := by
        rw [hJHx,Nat.add_one_sub_one]
        exact Nat.zero_lt_of_ne_zero kzero
      have this':= JHx.first_eq_top ▸ JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) this (Nat.sub_le (Nat.find JHx.fin_len) 1)
      exfalso
      have : JHx.filtration (Nat.find JHx.fin_len - 1) = ⊤ := Subtype.coe_inj.mp (Eq.mpr (id (congrArg (fun _a ↦ _a = ↑⊤) hnz)) (Eq.refl ⊤))
      exact (and_not_self_iff ((fun a b ↦ ↑a ≤ ↑b) ⊤ ⊤)).1 <| this ▸ this'
    else
    let JHfun : ℕ → Interval ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩ := fun n ↦
      if hn : n ≤ Nat.find JHx.fin_len - 1 then
        ⟨JHx.filtration n,⟨JHx.antitone hn,by simp⟩⟩
      else
        ⊥
    have JHfun_fin_len : ∃ N : ℕ, JHfun N = ⊥ := by
        simp only [JHfun]
        use Nat.find JHx.fin_len
        simp [lt_iff_not_le.1 <| Nat.sub_one_lt h1]
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
        have bitch : ↑(⊥ : (Interval ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩)) = (JHx.filtration (Nat.find JHx.fin_len - 1)).val := rfl
        rw [bitch] at this'
        apply Subtype.coe_inj.1
        simp only [← this']
      have := hweired ▸ this
      exact (lt_self_iff_false (JHx.filtration (Nat.find JHx.fin_len - 1))).1 this
    let JHres : JordanHolderFiltration (Resμ ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩ μ) := by
      refine { filtration := ?_, antitone := ?_, fin_len := ?_, strict_anti := ?_, first_eq_top := ?_, step_cond₁ := ?_, step_cond₂ := ?_ }
      · use JHfun
      · exact JHfun_antitone
      · exact JHfun_fin_len
      · intro i j hij hj
        simp only [JHfun,hhard ▸ hj,le_of_lt <| lt_of_lt_of_le hij (hhard ▸ hj)]
        simp
        exact JHx.strict_anti i j hij (le_trans (hhard ▸ hj) <| le_of_lt <| Nat.sub_one_lt h1)
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
        simp only [Resμ] at this
        rw [this]
        have this' := JHx.step_cond₁ (Nat.find JHx.fin_len - 1) (Nat.sub_one_lt h1)
        simp only [Resμ,Nat.sub_one_add_one h1] at this'
        simp only [Nat.find_spec JHx.fin_len] at this'
        have ntop : JHx.filtration (Nat.find JHx.fin_len - 1) < ⊤ := by
          have : Nat.find JHx.fin_len - 1 ≠ 0 := by
            by_contra t
            rw [t] at hk1
            linarith
          rw [← JHx.first_eq_top]
          exact JHx.strict_anti 0 (Nat.find JHx.fin_len - 1) (by linarith) (le_of_lt <| Nat.sub_one_lt h1)
        exact (((seesaw_useful (Resμ ⟨(x, ⊤), hx⟩ μ)) (inferInstance) ⊥
          (JHx.filtration (Nat.find JHx.fin_len - 1)) ⊤ ⟨bot_lt_iff_ne_bot.2 <| Nat.find_min JHx.fin_len (Nat.sub_one_lt h1),ntop⟩).2.2.1 this').2
      · intro i hi z hz hz'
        simp only [Resμ]
        have ilt : i < Nat.find JHx.fin_len := by
          rw [hhard] at hi
          exact Nat.lt_of_lt_pred hi
        have htemp : JHx.filtration (i + 1) < ⟨z.val,⟨le_trans (JHx.filtration (Nat.find JHx.fin_len - 1)).prop.1 z.prop.1,z.prop.2⟩⟩ := by
          simp only [JHfun] at hz
          simp [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi] at hz
          exact hz
        have htemp2 : ⟨z.val,⟨le_trans (JHx.filtration (Nat.find JHx.fin_len - 1)).prop.1 z.prop.1,z.prop.2⟩⟩ < JHx.filtration i := by
          simp only [JHfun,le_of_lt <| hhard ▸ hi] at hz'
          simp at hz'
          exact hz'
        have hnew := JHx.step_cond₂ i ilt ⟨z.val,⟨le_trans (JHx.filtration (Nat.find JHx.fin_len - 1)).prop.1 z.prop.1,z.prop.2⟩⟩ htemp htemp2
        simp [Resμ] at hnew
        simp only [JHfun]
        simp [Eq.mpr (id (congrArg (fun _a ↦ i + 1 ≤ _a) hhard.symm)) hi,le_of_lt <| hhard ▸ hi]
        exact hnew
    have res_len: Nat.find JHres.fin_len = k := by
      rw [hhard,hJHx,Nat.add_one_sub_one]
    have himportant := hk (JHx.filtration (Nat.find JHx.fin_len - 1)).val (lt_top_iff_ne_top.2 hnz) ⟨JHres,res_len⟩
    have JH_raw_first_top: JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JH.filtration 0 = ⊤ := by
      simp [JH.first_eq_top]

    let JH_raw : ℕ → Interval ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩ := fun n ↦ ⟨(JHx.filtration (Nat.find JHx.fin_len - 1) ⊔ JH.filtration n),⟨le_sup_left,le_top⟩⟩
    have JH_raw_antitone : Antitone JH_raw := by
      intro n1 n2 hn
      apply sup_le_sup_left
      exact JH.antitone hn
    have JH_raw_cond1 : ∀ n : ℕ, n < Nat.find JH.fin_len → (hn: JH_raw (n+1) < JH_raw n) → μ ⟨(JH_raw (n+1),JH_raw n),lt_iff_le_not_le.mpr hn⟩ = μ ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val,⊤),lt_top_iff_ne_top.2 hnz⟩ := by
      sorry
    have JH_raw_cond2 : ∀ n : ℕ, n < Nat.find JH.fin_len → (hn: JH_raw (n+1) < JH_raw n) → ∀ w : Interval ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩, (hw : JH_raw (n+1) < w) → (hw' : w < JH_raw n) → ¬ JH_raw n ≤ w := by sorry
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simp only [JH_raw,Resμ]
      simp [JH.first_eq_top]
      rfl
    have JH_raw_fin_len: JH_raw (Nat.find JH.fin_len) = ⊥ := by
      simp only [JH_raw]
      simp [Nat.find_spec JH.fin_len]
      rfl
    let JHfinal := function_wrapper JH_raw (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simp only [JHfinal,function_wrapper]
    have JHfinal_fin_len : ∃ N : ℕ, JHfinal N = ⊥ := by
        exact function_wrapper_prop1 JH_raw (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩) JH_raw_antitone JH_raw_first_top
    let JHFINAL : JordanHolderFiltration (Resμ ⟨((JHx.filtration (Nat.find JHx.fin_len - 1)).val, ⊤), lt_top_iff_ne_top.2 hnz⟩ μ) := by
      refine { filtration := ?_, antitone := ?_, fin_len := ?_, strict_anti := ?_, first_eq_top := ?_, step_cond₁ := ?_, step_cond₂ := ?_ }
      · exact JHfinal
      · exact function_wrapper_prop2 JH_raw (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩)
      · exact JHfinal_fin_len
      · intro i j hij hj
        simp only [JHfinal]
        exact function_wrapper_prop5 JH_raw JH_raw_first_top (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩) JH_raw_antitone i j hij hj
      · simp [*]
      · sorry
      · sorry
    have ha : Nat.find JHFINAL.fin_len < Nat.find JH.fin_len := by
      have : JHfinal (Nat.find JH.fin_len) = ⊥ := by
        simp only [JHfinal,function_wrapper]
        have : JH_raw (Nat.find JH.fin_len) = ⊥ := by
          simp only [JH_raw]
          simp [Nat.find_spec JH.fin_len]
          rfl
        have hweird := eq_bot_iff.2 <| this ▸ function_wrapper_prop3 JH_raw JH_raw_first_top (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JH.fin_len)
        exact hweird
      refine lt_of_le_of_ne ?_ ?_
      · exact Nat.find_min' JHFINAL.fin_len this
      · refine function_wrapper_prop4 JH_raw JH_raw_first_top (⟨Nat.find JH.fin_len,JH_raw_fin_len⟩) JH_raw_antitone (Nat.find JH.fin_len) JH_raw_fin_len ?_
        sorry
    exact lt_of_le_of_lt (himportant JHFINAL) ha

end impl
