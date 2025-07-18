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
    have : {p : ℒ | ∃ h : ⊥ < p, p < ⊤ ∧ μ ⟨(⊥,p),h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩}.Nonempty := sorry
    simp only [this]
    have this' := (hacc.wf.has_min _ this).choose_spec.1.2.2
    exact ((Or.resolve_left <| (Or.resolve_left <| (impl.prop4d6 μ).1 hμsl ⊥ (hacc.wf.has_min _ this).choose ⊤ ⟨(hacc.wf.has_min _ this).choose_spec.1.choose,(hacc.wf.has_min _ this).choose_spec.1.out.choose_spec.1⟩) (sorry)) (sorry)).2.symm
  · sorry





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
