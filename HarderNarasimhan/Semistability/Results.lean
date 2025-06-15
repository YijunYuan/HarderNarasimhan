import HarderNarasimhan.Semistability.Impl

lemma proposition_3_2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (x : ℒ) (z : ℒ) (h : x < z)
  (h' : μA μ ⟨(x , z) , h⟩ = ⊤)
  (a : ℒ) (hax : a < x) :
------------
  μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩
------------
  := impl.prop3d2 TotIntvl μ hμcvx x (in_TotIntvl x) z (in_TotIntvl z) h h' a (in_TotIntvl a) hax


alias corollary_3_3 := impl.cor3d3


lemma proposition_3_4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (hμDCC : μDCC μ) (hμcvx : IsConvex μ) :
------------
  (St μ).Nonempty
------------
  := impl.prop3d4 μ hμDCC TotIntvl hμcvx


lemma remark_3_5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (hxSt : x ∈ St μ)
  (y : ℒ) (hySt : y ∈ St μ) :
------------
  x = y
------------
  := impl.rmk3d5 μ TotIntvl x hxSt y hySt


lemma proposition_3_7 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (x : ℒ) (hxSt : x ∈ St μ) :
------------
  --`(1)`
  semistableI μ ⟨(⊥, x), lt_of_le_of_ne bot_le hxSt.out.choose_spec.choose⟩
  ∧
  --`(2)`
  ∀ y : ℒ, (hy : y > x) → ¬ μA μ ⟨(⊥ , x) , lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨(x, y), hy⟩
------------
  := ⟨impl.prop3d7₁ μ TotIntvl x hxSt, fun y hy ↦ impl.prop3d7₂ μ TotIntvl hμcvx x hxSt y (in_TotIntvl y) hy⟩


lemma proposition_3_8 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hz : ⊥ ≠ z) → IsAttained μ ⟨(⊥ , z) , lt_of_le_of_ne bot_le hz⟩) :
------------
  (
  --`(1)`
  IsTotal (St μ) (· ≤ ·) ∧ (μDCC μ → ∃ s : ℒ, IsGreatest (St μ) s)
  ) ∧
  --`(2)`
  ∀ x : ℒ, (hxSt : x ∈ St μ) →
  (∀ y : ℒ, (hxy : y > x) → μA μ ⟨(⊥ , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩)
------------
 := by
  constructor
  · constructor
    · cases' h with c1 c2
      · exact impl.prop3d8₁ μ TotIntvl hμcvx (Or.inl c1)
      · exact impl.prop3d8₁ μ TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz)
    · intro hμDCC
      cases' h with c1 c2
      · exact impl.prop3d8₁' μ hμDCC TotIntvl hμcvx (Or.inl c1)
      · exact impl.prop3d8₁' μ hμDCC TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz)
  · intro x hxSt y hxy
    cases' h with c1 c2
    · exact impl.prop3d8₂ μ TotIntvl hμcvx (Or.inl c1) x hxSt y (in_TotIntvl y) hxy
    · exact impl.prop3d8₂ μ TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz) x hxSt y (in_TotIntvl y) hxy
