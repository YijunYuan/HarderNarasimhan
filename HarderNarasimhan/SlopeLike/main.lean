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


class TotallyOrderedRealVectorSpace (V : Type) extends AddCommGroup V, Module ℝ V, LinearOrder V, PosSMulStrictMono ℝ V where
  elim_AddLeftMono : ∀ {y z : V} (x : V), y ≤ z → x + y ≤ x + z

instance {V : Type} [TotallyOrderedRealVectorSpace V] : AddLeftMono V where
  elim := fun x _ _ h ↦ TotallyOrderedRealVectorSpace.elim_AddLeftMono x h


noncomputable def μQuotient {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V): {p :ℒ × ℒ // p.1 < p.2} → DedekindMacNeilleCompletion V := fun
    z ↦
  if _ : r z > 0 then
    coe' ((r z)⁻¹ • d z)
  else ⊤


lemma μQuotient_helper {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V): ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z > 0 → ∃ (μ : V), (μQuotient r d) z = coe' μ ∧ (r z) • μ = (d z) := by
  intro z h
  use ((r z)⁻¹ • d z)
  constructor
  · simp [μQuotient, coe', h]
  · exact smul_inv_smul₀ (by aesop) (d z)


lemma prop4d8 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) → d ⟨(x, z), lt_trans h.1 h.2⟩ = d ⟨(x, y), h.1⟩ + d ⟨(y, z), h.2⟩ ∧ r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ + r ⟨(y, z), h.2⟩)
(h₂ : ∀ (x y :ℒ), (h : x < y) → r ⟨(x,y),h⟩ = 0 → d ⟨(x,y),h⟩ > 0)
: SlopeLike (μQuotient r d) := by
  let μ := μQuotient r d
  apply (prop4d6 μ).2
  intro x y z h
  cases' eq_zero_or_pos (r ⟨(x, z), lt_trans h.1 h.2⟩) with h' h'
  · have : r ⟨(x, y), h.1⟩ = 0 ∧ r ⟨(y, z), h.2⟩ = 0 := add_eq_zero.1 <| (h₁ x y z h).2 ▸ h'
    have : ¬ r ⟨(y, z), h.2⟩ > 0 ∧ ¬ r ⟨(x,y), h.1⟩ > 0:= by
      aesop
    have : μ ⟨(x, z), lt_trans h.1 h.2⟩ = ⊤ ∧ μ ⟨(x, y), h.1⟩ = ⊤ ∧ μ ⟨(y, z), h.2⟩ = ⊤ := by
      refine ⟨?_,⟨?_,?_⟩⟩
      · simp [μ,μQuotient, h']
      · simp [μ,μQuotient,this.2]
      · simp [μ,μQuotient,this.1]
    aesop
  · by_cases h'' : r ⟨(x, y), h.1⟩ > 0 ∧ r ⟨(y, z), h.2⟩ > 0
    · rcases μQuotient_helper r d ⟨(x, y), h.1⟩ h''.1 with ⟨μxy,⟨hxy₁,hxy₂⟩⟩
      rcases μQuotient_helper r d ⟨(y, z), h.2⟩ h''.2 with ⟨μyz,⟨hyz₁,hyz₂⟩⟩
      rcases μQuotient_helper r d ⟨(x, z), lt_trans h.1 h.2⟩ h' with ⟨μxz,⟨hxz₁,hxz₂⟩⟩
      have : r ⟨(x, y), h.1⟩ • μxz + r ⟨(y, z), h.2⟩ • μxz = r ⟨(x, y), h.1⟩ • μxy + r ⟨(y, z), h.2⟩ • μyz := add_smul (r ⟨(x, y), h.1⟩) (r ⟨(y, z), h.2⟩) μxz ▸ (h₁ x y z h).2 ▸ hxy₂ ▸ hyz₂ ▸ hxz₂ ▸ (h₁ x y z h).1
      simp [μ,hxy₁,hyz₁,hxz₁]
      by_cases hs : μxy < μxz
      · refine Or.inl ⟨hs,?_⟩
        have hs := (eq_sub_of_add_eq this) ▸ (smul_lt_smul_iff_of_pos_left h''.1).2 hs
        rw [lt_sub_iff_add_lt,add_lt_add_iff_left] at hs
        exact (smul_lt_smul_iff_of_pos_left h''.2).1 hs
      · by_cases hs' : μxy = μxz
        · refine Or.inr <| Or.inr <| ⟨hs',?_⟩
          simp [hs'] at this
          have : (r ⟨(y, z), h.2⟩)⁻¹ • (r ⟨(y, z), h.2⟩) • μxz = (r ⟨(y, z), h.2⟩)⁻¹ • (r ⟨(y, z), h.2⟩) • μyz := congrArg (HSMul.hSMul (r ⟨(y, z), h.right⟩)⁻¹) this
          rw [← smul_assoc,← smul_assoc] at this
          simp at this
          have invt : Invertible (r ⟨(y, z), h.2⟩) := by
            refine { invOf := ?_, invOf_mul_self := ?_, mul_invOf_self := ?_ }
            use (r ⟨(y, z), h.2⟩)⁻¹
            · aesop
            · exact (mul_eq_one_iff_eq_inv₀ <| ne_of_gt h''.2).2 rfl
            · exact (mul_eq_one_iff_inv_eq₀ <| ne_of_gt h''.2).2 rfl
          rw [inv_mul_cancel_of_invertible <| r ⟨(y, z), h.2⟩,one_smul,one_smul] at this
          exact this
        · have hs' : μxz < μxy := lt_of_not_le (Eq.mpr (id (congrArg (fun _a ↦ ¬_a) (propext le_iff_eq_or_lt))) (not_or.mpr ⟨hs', hs⟩))
          refine Or.inr <| Or.inl <| ⟨hs',?_⟩
          have hs' := (eq_sub_of_add_eq this) ▸ (smul_lt_smul_iff_of_pos_left h''.1).2 hs'
          rw [sub_lt_iff_lt_add,add_lt_add_iff_left] at hs'
          exact (smul_lt_smul_iff_of_pos_left h''.2).1 hs'
    · by_cases h''' : r ⟨(x, y), h.1⟩ = 0 ∧ r ⟨(y, z), h.2⟩ > 0
      · sorry
      · apply not_and_or.1 at h''
        apply not_and_or.1 at h'''
        have : ¬ r ⟨(x, y), h.1⟩ = 0 ↔ r ⟨(x, y), h.1⟩ > 0 := pos_iff_ne_zero.symm
        rw [this] at h'''
        have : ¬r ⟨(y, z), h.2⟩ > 0 := by tauto
        have : r ⟨(y, z), h.2⟩ = 0 := by aesop
        have this' : r ⟨(x, y), h.1⟩ > 0 := (add_zero <| r ⟨(x, y), h.1⟩) ▸ (this ▸ (h₁ x y z h).2) ▸ h'
        sorry
