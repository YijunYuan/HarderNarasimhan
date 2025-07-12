import HarderNarasimhan.SlopeLike.Defs


namespace impl
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
      exact imp_iff_not_or.1 fun h' ↦ by cases' (by tauto : μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩) with this this <;> [exact le_of_lt this.2; exact le_of_eq this.2.symm]
    · have : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ ↔ ¬¬ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ := Iff.symm not_not
      rw [this]
      refine imp_iff_not_or.1 fun h' ↦ ?_
      have : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩ := by tauto
      cases' this with this this <;> [exact le_of_lt this.2; exact le_of_eq this.2]
    · have : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ ↔ ¬¬ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩ := Iff.symm not_not
      rw [this]
      exact imp_iff_or_not.1 fun h' ↦ by cases' (by tauto : μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩ ∨ μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩) with this this <;> [exact le_of_lt this.1; exact le_of_eq this.1.symm]


lemma not_top_of_Nontrivial_TotallyOrderedRealVectorSpace {V : Type} [TotallyOrderedRealVectorSpace V] [hnt: Nontrivial V] : ∀ v : V, coe' v < (⊤ : DedekindMacNeilleCompletion V) := by
  intro v
  rcases hnt.exists_pair_ne with ⟨v₁, v₂, hne⟩
  let v₀ := if v₁ < v₂ then v₂ - v₁ else v₁ - v₂
  have hpos : v₀ > 0 := by
    by_cases h : v₁ < v₂
    · simp [v₀,h]
    · simp [v₀,h]
      exact (eq_or_lt_of_not_lt h).resolve_left hne
  by_contra!
  exact not_top_lt <| ((le_iff_eq_or_lt.1 le_top).resolve_right this) ▸ (coe'.lt_iff_lt.2 <| lt_add_of_pos_right v hpos)


lemma μQuotient_helper {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V): ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z > 0 → ∃ (μ : V), (μQuotient r d) z = coe' μ ∧ (r z) • μ = (d z) :=
  fun z h ↦ ⟨(r z)⁻¹ • d z,⟨by simp [μQuotient, coe', h], smul_inv_smul₀ (by aesop) (d z)⟩⟩


lemma prop4d8 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{V : Type} [TotallyOrderedRealVectorSpace V] [Nontrivial V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) → d ⟨(x, z), lt_trans h.1 h.2⟩ = d ⟨(x, y), h.1⟩ + d ⟨(y, z), h.2⟩ ∧ r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ + r ⟨(y, z), h.2⟩)
(h₂ : ∀ (x y :ℒ), (h : x < y) → r ⟨(x,y),h⟩ = 0 → d ⟨(x,y),h⟩ > 0)
: SlopeLike (μQuotient r d) := by
  let μ := μQuotient r d
  refine (prop4d6 μ).2 fun x y z h ↦ ?_
  cases' eq_zero_or_pos (r ⟨(x, z), lt_trans h.1 h.2⟩) with h' h'
  · have : r ⟨(x, y), h.1⟩ = 0 ∧ r ⟨(y, z), h.2⟩ = 0 := add_eq_zero.1 <| (h₁ x y z h).2 ▸ h'
    have : ¬ r ⟨(y, z), h.2⟩ > 0 ∧ ¬ r ⟨(x,y), h.1⟩ > 0 := by aesop
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
      have := add_smul (r ⟨(x, y), h.1⟩) (r ⟨(y, z), h.2⟩) μxz ▸ (h₁ x y z h).2 ▸ hxy₂ ▸ hyz₂ ▸ hxz₂ ▸ (h₁ x y z h).1
      simp [μ,hxy₁,hyz₁,hxz₁]
      by_cases hs : μxy < μxz
      · exact Or.inl ⟨hs,(smul_lt_smul_iff_of_pos_left h''.2).1 <| (add_lt_add_iff_left <| r ⟨(x, y), h.1⟩ • μxy).1 <| lt_sub_iff_add_lt.1 <| (eq_sub_of_add_eq this) ▸ (smul_lt_smul_iff_of_pos_left h''.1).2 hs⟩
      · by_cases hs' : μxy = μxz
        · refine Or.inr <| Or.inr <| ⟨hs',?_⟩
          simp [hs'] at this
          exact smul_right_injective V (ne_of_lt h''.2).symm this
        · have hs' : μxz < μxy := lt_of_not_le (Eq.mpr (id (congrArg (fun _a ↦ ¬_a) (propext le_iff_eq_or_lt))) (not_or.mpr ⟨hs', hs⟩))
          exact Or.inr <| Or.inl <| ⟨hs',(smul_lt_smul_iff_of_pos_left h''.2).1 <| (add_lt_add_iff_left <| r ⟨(x, y), h.1⟩ • μxy).1 <| sub_lt_iff_lt_add.1 <| (eq_sub_of_add_eq this) ▸ (smul_lt_smul_iff_of_pos_left h''.1).2 hs'⟩
    · by_cases h''' : r ⟨(x, y), h.1⟩ = 0 ∧ r ⟨(y, z), h.2⟩ > 0
      · have h2 : μ ⟨(x, y), h.1⟩ = ⊤ := by simp [μ, μQuotient, h'''.1]
        have h4 := (zero_add <| r ⟨(y, z), h.2⟩) ▸ h'''.1 ▸ (h₁ x y z h).2
        cases' le_iff_eq_or_lt.1 (h2 ▸ le_top : μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(x, y), h.1⟩) with h3 h3
        · rcases μQuotient_helper r d ⟨(x,z),lt_trans h.1 h.2⟩ (h4 ▸ h'''.2) with ⟨w,⟨hw₁,_⟩⟩
          simp [μ] at h3; simp [μ] at h2
          exact False.elim (not_top_lt ((h2 ▸ h3 ▸ hw₁).symm ▸ not_top_of_Nontrivial_TotallyOrderedRealVectorSpace w))
        · refine Or.inr <| Or.inl <| ⟨h3,?_⟩
          simp [μ,μQuotient,Eq.mpr (id (congrArg (fun _a ↦ _a > 0) h4)) h'''.right,h'''.2]
          exact h4 ▸ ((smul_lt_smul_iff_of_pos_left <| Right.inv_pos.mpr h').2 <| (h₁ x y z h).1 ▸ lt_add_of_pos_left (d ⟨(y, z), h.right⟩) <| h₂ x y h.1 h'''.1)
      · apply not_and_or.1 at h''
        apply not_and_or.1 at h'''
        simp [pos_iff_ne_zero.symm] at h'''
        have : r ⟨(y, z), h.2⟩ = 0 := by aesop
        have this' := (add_zero <| r ⟨(x, y), h.1⟩) ▸ (this ▸ (h₁ x y z h).2) ▸ h'
        have h2 : μ ⟨(y, z), h.2⟩ = ⊤ := by simp [μ, μQuotient, this]
        have h4 := (add_zero <| r ⟨(x, y), h.1⟩) ▸ this ▸ (h₁ x y z h).2
        cases' le_iff_eq_or_lt.1 (h2 ▸ le_top : μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(y, z), h.2⟩) with h3 h3
        · rcases μQuotient_helper r d ⟨(x,z),lt_trans h.1 h.2⟩ (h4 ▸ this') with ⟨w,hw₁,_⟩
          simp [μ] at h3; simp [μ] at h2
          exact False.elim (not_top_lt ((h2 ▸ h3 ▸ hw₁).symm ▸ not_top_of_Nontrivial_TotallyOrderedRealVectorSpace w))
        · refine Or.inl <| ⟨?_,h3⟩
          simp [μ,μQuotient,this',Eq.mpr (id (congrArg (fun _a ↦ _a > 0) h4))]
          exact h4 ▸ ((smul_lt_smul_iff_of_pos_left <| Right.inv_pos.mpr h').2 <| (h₁ x y z h).1 ▸ lt_add_of_pos_right (d ⟨(x, y), h.1⟩) <| h₂ y z h.2 this)
end impl
