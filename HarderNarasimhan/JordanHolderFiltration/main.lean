import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl
import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
open Classical


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
  have this_new := (List.TFAE.out (impl.thm4d21 μ hμsl (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf)) (fun f saf ↦ Exists.casesOn (hdc f saf) fun N hN ↦ Exists.intro N (Eq.symm hN ▸ le_top))) 0 4).2 hst
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



theorem thm4d25 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : Semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∃ y : ℕ → ℒ, ∃ say : StrictAnti y, ∃ hfl : (∃ N :ℕ, y N =⊥),
(
  y 0 = ⊤
) ∧ (
  ∀ i : ℕ, (hpos : 1 ≤ i) → i ≤ Nat.find hfl →
  (
    μ ⟨(y i, y (i - 1)), say <| Nat.sub_one_lt_of_lt hpos⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  ) ∧ (
    ∀ z : ℒ, (h' : y i < z) → (h'' : z < y (i - 1)) → μ ⟨(y i, z), h'⟩ = μ ⟨(y i, y (i - 1)), say <| Nat.sub_one_lt_of_lt hpos⟩
  )
)
:= sorry






class JordanHolderFiltration {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) {hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤}
{hμsl : SlopeLike μ} {hst : Semistable μ}
{hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤} where
  filtration : ℕ → ℒ
  strict_anti : StrictAnti filtration
  fin_len : ∃ N : ℕ, filtration N =⊥
  first_top : filtration 0 = ⊤
  step_cond₁ : ∀ i : ℕ, (hpos : 1 ≤ i) → i ≤ Nat.find fin_len →
    (μ ⟨(filtration i, filtration (i - 1)), strict_anti <| Nat.sub_one_lt_of_lt hpos⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩)
  step_cond₂ : ∀ i : ℕ, (hpos : 1 ≤ i) → i ≤ Nat.find fin_len →
    ∀ z : ℒ, (h' : filtration i < z) → (h'' : z < filtration (i - 1)) →
    μ ⟨(filtration i, z), h'⟩ = μ ⟨(filtration i, filtration (i - 1)), strict_anti <| Nat.sub_one_lt_of_lt hpos⟩


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} {hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤}
{hμsl : SlopeLike μ} {hst : Semistable μ}
{hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤}
: Nonempty (@JordanHolderFiltration ℒ _ _ _ _ S _ μ hμ hμsl hst hdc) := by
  refine exists_true_iff_nonempty.mp ?_
  use JordanHolderFiltration.mk (thm4d25 μ hμ hμsl hst hdc).choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.1 (fun i hpos h'↦ ((thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.2 i hpos h').1) (fun i hpos h'↦ ((thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.2 i hpos h').2)


lemma rmk4d26 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} {hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤}
{hμsl : SlopeLike μ} {hst : Semistable μ}
{hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤} :
∀ f₁ f₂ : @JordanHolderFiltration ℒ _ _ _ _ S _ μ hμ hμsl hst hdc, Nat.find f₁.fin_len = Nat.find f₂.fin_len
:= sorry
