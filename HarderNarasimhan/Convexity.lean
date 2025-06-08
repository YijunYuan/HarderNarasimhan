import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℒ, ∀ y : ℒ, InInterval I x → InInterval I y → (h : ¬ x ≤ y) → μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩


lemma Convex_of_Convex_large {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I₁ : {p : ℒ × ℒ // p.1 < p.2})
(I₂ : {p : ℒ × ℒ // p.1 < p.2})
(hI : I₁.val.1 ≤ I₂.val.1 ∧ I₂.val.2 ≤ I₁.val.2)
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
IsConvexI I₁ μ → IsConvexI I₂ μ := fun hμcvx₁ x y hxI hyI hxy ↦ hμcvx₁ x y ⟨le_trans hI.1 hxI.1, le_trans hxI.2 hI.2⟩ ⟨le_trans hI.1 hyI.1, le_trans hyI.2 hI.2⟩ hxy


lemma lem2d4₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (w : ℒ) (hxw : ¬ x ≤ w)
  (u : ℒ) (huxw : u ≤ x ⊓ w) :
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
  have h1 : μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
    apply sInf_le_sInf
    intro t ht
    rcases ht with ⟨a, ha, _⟩
    use a, ⟨⟨le_trans huxw ha.1.1, ha.1.2⟩, ha.2⟩
  have h2 : μA μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
    apply sInf_le
    use x ⊓ w, ⟨⟨le_rfl, le_of_lt (inf_lt_left.2 hxw)⟩, ne_of_lt (inf_lt_left.2 hxw)⟩
  exact le_trans h1 h2


lemma lem2d4₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (w : ℒ) (hwI : InInterval I w)
  (hxw : ¬ x ≤ w)
  (t : ℒ)
  (hxwt : x ⊔ w ≤ t) :
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by
    have h : ∀ b : ℒ, (h' : x ⊓ w < b ∧ b ≤ x) →
        μ ⟨(x ⊓ w, b), h'.1⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by
      intro b hb
      have hh : x ⊓ w = b ⊓ w := by
        apply le_antisymm
        · nth_rw 1 [← inf_idem w]
          rw [← inf_assoc]
          exact inf_le_inf_right w <| le_of_lt hb.1
        · exact inf_le_inf_right w hb.2
      simp [hh]
      have hbnlew : ¬ b ≤ w := inf_lt_left.mp
        ((congrArg (fun _a ↦ _a < b) (hh.symm)) ▸ hb.1)
      have hfinal : μ ⟨(w, b ⊔ w), IsConvexI._proof_2 b w hbnlew⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt (right_lt_sup.mpr hxw)⟩ := by
        apply le_sSup
        use b ⊔ w, ⟨⟨le_sup_right, le_trans (sup_le_sup_right hb.2 w) hxwt⟩, (mt right_eq_sup.1) <| inf_lt_left.1 <| lt_of_eq_of_lt hh.symm hb.1⟩
      apply le_trans (hμcvx b w ⟨le_of_lt (lt_of_le_of_lt (le_inf hxI.1 hwI.1) hb.1), le_trans hb.2 hxI.2⟩ hwI hbnlew) hfinal
    apply sSup_le
    rintro b ⟨_, ⟨hf₁, hf₂⟩⟩
    rw [hf₂.symm]
    apply h
    exact ⟨lt_of_le_of_ne hf₁.1.1 hf₁.2, hf₁.1.2⟩


lemma lem2d4₃I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (w : ℒ) (hwI : InInterval I w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huxw : u ≤ x ⊓ w):
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩ := by
  apply le_sInf
  rintro imy ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [← hy₂]
  have h₁ : ¬ x ≤ y := by
    by_contra h
    exact lt_irrefl (x ⊔ w) (lt_of_le_of_lt (sup_le_sup_right h w) (lt_of_eq_of_lt (sup_eq_left.2 hy₁.1.1) (lt_of_le_of_ne hy₁.1.2 hy₁.2)))
  apply le_trans
  · apply lem2d4₁ μ x y h₁ u (le_trans huxw <| inf_le_inf_left x hy₁.1.1)
  · apply lem2d4₂I I μ hμcvx x hxI y ⟨le_trans hwI.1 hy₁.1.1, le_trans hy₁.1.2 <| sup_le hxI.2 hwI.2⟩ h₁ (x ⊔ w) (sup_le le_sup_left hy₁.1.2)


lemma lem2d4I (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x) (hx : I.val.1 ≠ x)
  (w : ℒ) (hwI : InInterval I w) (hw : I.val.1 ≠ w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huI : InInterval I u)
  (t : ℒ) (htI : InInterval I t)
  (hut : u ≤ t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ ∧
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩ :=
  ⟨lem2d4₁ μ x w hxw u huxw, ⟨lem2d4₂I I μ hμcvx x hxI w hwI hxw t hxwt, lem2d4₃I I μ hμcvx x hxI w hwI hxw u huxw⟩⟩


lemma rmk2d5₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ) :
  IsConvexI I (μmax μ)  := fun x y hxI hyI hxy ↦ lem2d4₂I I μ hμcvx x hxI y hyI hxy (x ⊔ y) le_rfl


lemma rmk2d5₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ) :
  μmax μ I = μmax (μmax μ) I := by
  apply eq_of_le_of_le
  · apply le_sSup
    use I.val.2, ⟨⟨le_of_lt I.prop, le_refl I.val.2⟩, ne_of_lt I.prop⟩
  · apply sSup_le
    simp
    intro b v hv res
    rw [← res]
    have h : μmax μ ⟨(v ⊓ I.val.1, v), inf_lt_left.2 (not_le_of_gt (lt_of_le_of_ne hv.1.1 hv.2))⟩ ≤ μmax μ ⟨(I.val.1, I.val.2), gt_of_ge_of_gt (le_of_eq_of_le (sup_eq_left.2 hv.1.1) hv.1.2) (right_lt_sup.2 (not_le_of_gt (lt_of_le_of_ne hv.1.1 hv.2)))⟩ :=
      lem2d4₂I I μ hμcvx v hv.1 I.val.1 ⟨le_rfl, le_of_lt I.prop⟩ (not_le_of_gt (lt_of_le_of_ne hv.1.1 hv.2)) I.val.2 (le_of_eq_of_le (sup_eq_left.2 hv.1.1) hv.1.2)
    simp only [inf_eq_right.2 hv.1.1] at h
    exact h


lemma rmk2d5₃ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ) :
  μA μ I = μA (μmax μ) I := by
  apply eq_of_le_of_le
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    use a, ha
    apply rmk2d5₂ ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩
    exact Convex_of_Convex_large I ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩ ⟨ha.1.1, le_rfl⟩ μ hμcvx
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    use a, ha
    rw [← rmk2d5₂ ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩]
    exact Convex_of_Convex_large I ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩ ⟨ha.1.1, le_rfl⟩ μ hμcvx


lemma prop2d6₀ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩  := by
  apply sInf_le_sInf
  simp
  intro u v hv hu
  rw [← hu]
  use v, ⟨⟨le_of_lt (lt_of_lt_of_le h.1 hv.1.1), hv.1.2⟩, hv.2⟩


lemma prop2d6₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z) :
  (μA μ ⟨(x, y), h.1⟩ ⊓ (μA μ ⟨(y, z), h.2⟩)) ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ := by
  apply le_sInf_iff.2
  rintro d ⟨a, ha, rfl⟩
  by_cases hya : y ≤ a
  · apply le_trans inf_le_right
    apply sInf_le
    use a, ⟨⟨hya, ha.1.2⟩, ha.2⟩
  · exact le_trans inf_le_left <| le_trans (lem2d4₁ μ y a hya x <| le_inf (le_of_lt h.1) ha.1.1) (lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha.1.1, le_trans ha.1.2 hzI.2⟩ hya z <| sup_le (le_of_lt h.2) ha.1.2)


lemma prop2d6₂1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x, y), h.1⟩ ≥ μA μ ⟨(y, z), h.2⟩) :
  μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ := le_antisymm (le_of_eq_of_le (inf_eq_right.2 h').symm (prop2d6₁ I μ hμcvx x hxI y hyI z hzI h)) (prop2d6₀ μ x y z h)


lemma prop2d6₂2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩) :
  μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩ := ⟨le_of_eq_of_le (inf_eq_left.mpr (le_of_lt h')).symm (prop2d6₁ I μ hμcvx x hxI y hyI z hzI h), prop2d6₀ μ x y z h⟩


lemma comparable_iff {L : Type} [PartialOrder L] (x : L) (y : L) (h : IsComparable x y) : x < y ∨ y ≤ x := by
  simp [IsComparable] at h
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt] at h
  nth_rw 2 [or_comm] at h
  rw [or_assoc] at h
  nth_rw 2 [←or_assoc, eq_comm] at h
  rw [or_self, eq_comm, ← le_iff_eq_or_lt] at h
  exact h


lemma prop2d6₃ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : (IsComparable (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩)) ∨ (IsAttainable μ ⟨(x, z), lt_trans h.1 h.2⟩)) :
  μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨
  (μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
   μA μ ⟨(x, z), lt_trans h.1 h.2⟩ < μA μ ⟨(y, z), h.2⟩) := by
  cases' h' with h₁ h₂
  · apply comparable_iff (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩) at h₁
    by_cases h₂ : μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
    · exact Or.inl h₂
    · right
      have h₃ : μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩ := Or.resolve_right h₁ (fun hcontra ↦
      h₂ (prop2d6₂1 I μ hμcvx x hxI y hyI z hzI h hcontra))
      have h₄ : μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩ := prop2d6₂2 I μ hμcvx x hxI y hyI z hzI h h₃
      exact ⟨h₄.1, lt_of_le_of_ne h₄.2 (Ne.symm h₂)⟩
  · rcases h₂ with ⟨a, ⟨ha₁, ⟨ha₂, hres⟩⟩⟩
    apply or_iff_not_imp_left.2
    intro hnot
    have h' : ¬ y ≤ a := by
      by_contra hcontra
      have h'' : μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ := by
        have h''' : μA μ ⟨(y, z), h.2⟩ ≤ μmax μ ⟨(a, z), lt_of_le_of_ne ha₁.2 ha₂⟩ := by
          apply sInf_le
          use a , ⟨⟨hcontra, ha₁.2⟩, ha₂⟩
        exact eq_of_le_of_le (le_of_le_of_eq h''' hres) (prop2d6₀ μ x y z h)
      exact hnot h''
    constructor
    · exact le_of_le_of_eq (le_trans (lem2d4₁ μ y a h' x (le_inf (le_of_lt h.1) ha₁.1)) <| lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha₁.1, le_trans ha₁.2 hzI.2⟩ h' z <| sup_le (le_of_lt h.2) ha₁.2) hres
    · exact lt_of_le_of_ne (prop2d6₀ μ x y z h) <| Ne.symm hnot


lemma rmk2d7 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S] [LinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI ⟨(⊥, ⊤), bot_lt_top⟩ μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥, x), h.1⟩ > μA μ ⟨(⊥, ⊤), bot_lt_top⟩) :
  μA μ ⟨(x, ⊤), h.2⟩ = μA μ ⟨(⊥, ⊤), bot_lt_top⟩ := by

  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y) :
  μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ⊓ μA μ ⟨(u, y), h.2⟩ :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y)
  (hcpb: μA μ ⟨(u, x), h.1⟩ ≤ μA μ ⟨(u, y), h.2⟩ ∨
         μA μ ⟨(u, x), h.1⟩ ≥ μA μ ⟨(u, y), h.2⟩ ∨
         (∃ v : S, v = μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩)) :
  μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ∨
  μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ :=
  sorry
