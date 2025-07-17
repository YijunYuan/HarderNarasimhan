import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Defs


open Classical

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
