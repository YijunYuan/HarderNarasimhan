import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl


lemma lemma_2_4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (x : ℒ) (w : ℒ) (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ)
  (huxw : u ≤ x ⊓ w) (hxwt : x ⊔ w ≤ t) :
------------
  (
  --`(2.2)`
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩
  ) ∧
  --`(2.3)`
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩
------------
  := by
  simp only [IsConvex] at hμcvx
  constructor
  · constructor
    · exact impl.lem2d4₁ μ x w hxw u huxw
    · exact impl.lem2d4₂I TotIntvl μ hμcvx x (in_TotIntvl x) w (in_TotIntvl w) hxw t hxwt
  · exact impl.lem2d4₃I TotIntvl μ hμcvx x (in_TotIntvl x) w (in_TotIntvl w) hxw u huxw


lemma remark_2_5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ) :
------------
  IsConvex (μmax μ) ∧
  ∀  I : {p : ℒ × ℒ // p.1 < p.2},
    μmax μ I = μmax (μmax μ) I ∧ μA μ I = μA (μmax μ) I
------------
  := by
  simp only [IsConvex] at hμcvx
  constructor
  · exact impl.rmk2d5₁ TotIntvl μ hμcvx
  · intro I
    constructor
    · exact impl.rmk2d5₂ I μ (Convex_of_Convex_large TotIntvl I ⟨bot_le,le_top⟩ μ hμcvx)
    · exact impl.rmk2d5₃ I μ (Convex_of_Convex_large TotIntvl I ⟨bot_le,le_top⟩ μ hμcvx)


lemma proposition_2_6 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
------------
  --`(2.4)`
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩ ∧
  (
  IsConvex μ →
  --`(a)`
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≥ (μA μ ⟨(x, y), h.1⟩ ⊓ (μA μ ⟨(y, z), h.2⟩))
  ∧ (
  --`(b)`
  (
  μA μ ⟨(x, y), h.1⟩ ≥ μA μ ⟨(y, z), h.2⟩ →
    μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
  ) ∧ (
  μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩ →
    μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
    μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩
  )
  ) ∧ (
  --`(c)`
  IsComparable (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩) ∨
  IsAttained μ ⟨(x, z), lt_trans h.1 h.2⟩ →
    μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨
    (μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
     μA μ ⟨(x, z), lt_trans h.1 h.2⟩ < μA μ ⟨(y, z), h.2⟩)
    )
  )
------------
:= by
  constructor
  · exact impl.prop2d6₀ μ x y z h
  · intro hμcvx
    simp only [IsConvex] at hμcvx
    constructor
    · exact impl.prop2d6₁I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) z (in_TotIntvl z) h
    · constructor
      · constructor
        · exact impl.prop2d6₂I₁ TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) z (in_TotIntvl z) h
        · exact impl.prop2d6₂I₂ TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) z (in_TotIntvl z) h
      · exact impl.prop2d6₃I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) z (in_TotIntvl z) h


lemma remark_2_7 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥, x), h.1⟩ > μA μ ⟨(⊥, ⊤), bot_lt_top⟩) :
------------
  μA μ ⟨(x, ⊤), h.2⟩ = μA μ ⟨(⊥, ⊤), bot_lt_top⟩
------------
:= by
  simp only [IsConvex] at hμcvx
  exact impl.rmk2d7 μ hμcvx x h h'


lemma proposition_2_8 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h : u < x ∧ u < y) :
------------
  --`(a)`
  μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ⊓ μA μ ⟨(u, y), h.2⟩
  ∧ (
  --`(b)`
  IsComparable (μA μ ⟨(u, x), h.1⟩) (μA μ ⟨(u, y), h.2⟩) ∨
  IsAttained μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ →
    μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ∨
    μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, y), h.2⟩
  )
------------
:= by
  simp only [IsConvex] at hμcvx
  constructor
  · exact impl.prop2d8₁I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) u (in_TotIntvl u) h
  · exact impl.prop2d8₂I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) u (in_TotIntvl u) h
