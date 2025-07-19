import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl


open Classical


noncomputable def JHFil {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : semistable μ)
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
(hμsl : SlopeLike μ) (hst : semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∀ k : ℕ, JHFil μ hμ hμsl hst hdc k > ⊥ → JHFil μ hμ hμsl hst hdc k > JHFil μ hμ hμsl hst hdc (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simp only [h]
    exact hk

lemma fuck {α : Type} {a b c : α} (h₁: a = b) (h₂: c = b) : a = c := Eq.symm
  <| (congrArg (fun _a ↦ c = _a) h₁.symm) ▸ h₂


lemma JHFil_prop₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : semistable μ)
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
    · simp only [this]
      simp
  · intro hk'
    have jh_kp1_ntop : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ hμ hμsl hst hdc k ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty := by
      by_contra!
      simp only [JHFil,this] at hk'
      simp [*] at hk'
    have jh_kp1_ntop' : JHFil μ hμ hμsl hst hdc k > ⊥ := by
      refine lt_trans hk' ?_
      simp only [JHFil,jh_kp1_ntop]
      exact (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1
    have k_prop := hk jh_kp1_ntop'
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
          simp only [stupid]
          simp only [JHFil,jh_kp1_ntop]
          simp
        · apply not_and_iff_not_or_not.2
          refine Or.inl ?_
          simp only [stupid]
          simp only [JHFil,jh_kp1_ntop]
          simp
      conv_lhs =>
        arg 1
        arg 1
        arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp
      simp at hfinal
      rw [← hfinal]
      simp only [JHFil,jh_kp1_ntop]
      simp
      simp at bot_jh_kp1_eq_ans
      exact bot_jh_kp1_eq_ans
    · conv_lhs =>
        arg 1
        arg 1
        arg 1
        unfold JHFil
        simp only [jh_kp2_ntop]
        simp
      induction' k with r hr
      · unfold JHFil
        simp only [jh_kp1_ntop]
        have this' := (hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.2.2
        simp
        have : μ ⟨(⊥, (hacc.wf.has_min _ jh_kp1_ntop).choose), by
          simp only [JHFil] at jh_kp1_ntop
          simp only [JHFil,jh_kp1_ntop] at hk'
          simp at hk'
          simp
          exact hk'⟩ = μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
            refine ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ jh_kp1_ntop).choose ⊤ ⟨(hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.choose,(hacc.wf.has_min _ jh_kp1_ntop).choose_spec.1.out.choose_spec.1⟩) ?_) ?_).1
            · apply not_and_iff_not_or_not.2
              refine Or.inl ?_
              simp
              simp at this'
              exact le_of_eq this'.symm
            · apply not_and_iff_not_or_not.2
              refine Or.inl ?_
              simp
              simp at this'
              exact le_of_eq this'
        simp at this
        exact this
      · #check hr sorry sorry sorry sorry sorry sorry sorry

        sorry




lemma JHFil_fin_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc: WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : semistable μ)
(hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤) :
∃ N : ℕ, JHFil μ hμ hμsl hst hdc N = ⊥ := by
  by_contra hc
  simp at hc
  rcases hdc (fun n => JHFil μ hμ hμsl hst hdc n) <| strictAnti_of_add_one_lt <| fun n _ ↦ JHFil_anti_mono μ hμ hμsl hst hdc n (bot_lt_iff_ne_bot.2 <| hc n) with ⟨N, hN⟩

  sorry


theorem thm4d25 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
(hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤)
(hμsl : SlopeLike μ) (hst : semistable μ)
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
{hμsl : SlopeLike μ} {hst : semistable μ}
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
{hμsl : SlopeLike μ} {hst : semistable μ}
{hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤}
: Nonempty (@JordanHolderFiltration ℒ _ _ _ _ S _ μ hμ hμsl hst hdc) := by
  refine exists_true_iff_nonempty.mp ?_
  use JordanHolderFiltration.mk (thm4d25 μ hμ hμsl hst hdc).choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose (thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.1 (fun i hpos h'↦ ((thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.2 i hpos h').1) (fun i hpos h'↦ ((thm4d25 μ hμ hμsl hst hdc).choose_spec.choose_spec.choose_spec.2 i hpos h').2)


lemma rmk4d26 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} {hμ : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤}
{hμsl : SlopeLike μ} {hst : semistable μ}
{hdc: ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤} :
∀ f₁ f₂ : @JordanHolderFiltration ℒ _ _ _ _ S _ μ hμ hμsl hst hdc, Nat.find f₁.fin_len = Nat.find f₂.fin_len
:= sorry
