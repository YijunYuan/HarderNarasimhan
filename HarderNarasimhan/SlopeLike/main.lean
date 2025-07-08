import HarderNarasimhan.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.NNReal.Basic
import HarderNarasimhan.DedekindMacNeilleCompletion

def SlopeLike {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop := ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
(
  μ ⟨(x, y), h.1⟩ ≤ μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨ μ ⟨(y, z), h.2⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨ μ ⟨(y, z), h.2⟩ ≤ μ ⟨(x, z), lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ ∨ μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(y, z), h.2⟩
) ∧ (
  μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(x, y), h.1⟩ ∨ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩
)


lemma prop4d6 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S):
SlopeLike μ ↔ ∀ (x y z : ℒ), (h : x < y ∧ y < z) → (
  μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩
) := by
  constructor
  · intro sl x y z h
    have sl := sl x y z h
    by_cases h' : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩
    · exact Or.inl ⟨h', Or.resolve_left sl.2.2.2 (not_le_of_lt h')⟩
    · by_cases h'' : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩
      · have := not_le_of_lt h''
        tauto
      · have h₁ := not_lt_of_ge <| Or.resolve_left sl.2.1 h'
        exact Or.inr <| Or.inr ⟨Eq.symm <| eq_of_le_of_not_lt (Or.resolve_right sl.2.2.2 h₁) h'', eq_of_le_of_not_lt (by tauto) h₁⟩
  · intro seesaw x y z h
    have seesaw := seesaw x y z h
    refine ⟨?_,⟨?_,⟨?_,?_⟩⟩⟩
    · have : μ ⟨(y, z), h.2⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ↔ ¬¬ μ ⟨(y, z), h.2⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ := Iff.symm not_not
      rw [this]
      refine imp_iff_or_not.1 fun h' ↦ ?_
      have : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩ := by tauto
      cases' this with this this <;> [exact le_of_lt this.1; exact le_of_eq this.1]
    · have : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ↔ ¬¬ μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ := Iff.symm not_not
      rw [this]
      refine imp_iff_not_or.1 fun h' ↦ ?_
      have : μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩ := by tauto
      cases' this with this this <;> [exact le_of_lt this.2; exact le_of_eq this.2.symm]
    · have : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ ↔ ¬¬ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ := Iff.symm not_not
      rw [this]
      refine imp_iff_not_or.1 fun h' ↦ ?_
      have : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩ := by tauto
      cases' this with this this <;> [exact le_of_lt this.2; exact le_of_eq this.2]
    · have : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ ↔ ¬¬ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ := Iff.symm not_not
      rw [this]
      refine imp_iff_or_not.1 fun h' ↦ ?_
      have : μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩ := by tauto
      cases' this with this this <;> [exact le_of_lt this.1; exact le_of_eq this.1.symm]

class TotallyOrderedRealVectorSpace (V : Type) extends AddCommMonoid V, Module ℝ V, LinearOrder V where
  add_le : ∀ {y z : V} (x : V), y ≤ z → x + y ≤ x + z
  scalar_le : ∀ {y z : V} (c : ℝ), c ≥ 0 → c • y ≤ c • z



noncomputable def μQuotient {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V): {p :ℒ × ℒ // p.1 < p.2} → DedekindMacNeilleCompletion V := fun
    z ↦
  if _ : r z > 0 then ↑((r z)⁻¹ • d z) else ⊤



lemma prop4d8 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) → d ⟨(x, z), lt_trans h.1 h.2⟩ = d ⟨(x, y), h.1⟩ + d ⟨(y, z), h.2⟩ ∧ r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ + r ⟨(y, z), h.2⟩)
(h₂ : ∀ (x y :ℒ), (h : x < y) → r ⟨(x,y),h⟩ = 0 → d ⟨(x,y),h⟩ > 0)
: SlopeLike (μQuotient r d) := by
  intro x y z h
  refine ⟨?_,⟨?_,⟨?_,?_⟩⟩⟩
  · sorry
  · sorry
  · sorry
  · sorry
