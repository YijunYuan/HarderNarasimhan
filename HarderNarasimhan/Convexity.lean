import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℒ, ∀ y : ℒ, InInterval I x → InInterval I y → (h : ¬ x ≤ y) → μ ⟨(x ⊓ y , x) , inf_lt_left.2 h⟩ ≤ μ ⟨(y,x ⊔ y) , right_lt_sup.2 h⟩


lemma lem2d4I (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x) (hx : I.val.1 ≠ x)
  (w : ℒ) (hwI : InInterval I w) (hw : I.val.1 ≠ w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huI : InInterval I u)
  (t : ℒ) (huI : InInterval I t)
  (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ ∧
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by
  constructor
  · have h1 : μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ := by
      apply sInf_le_sInf
      intro t ht
      rcases ht with ⟨a, ha, _⟩
      use a , ⟨⟨le_trans huxw ha.1.left,ha.1.2⟩, ha.2⟩
    have h2 : μA μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ := by
      apply sInf_le
      use x ⊓ w, ⟨⟨le_rfl,le_of_lt (inf_lt_left.2 hxw)⟩ ,ne_of_lt (inf_lt_left.2 hxw)⟩
    exact le_trans h1 h2
  · constructor
    · have h : ∀ b : ℒ, (h' : x ⊓ w < b ∧ b ≤ x) →
        μ ⟨(x ⊓ w , b) , h'.1⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by sorry
      apply sSup_le
      rintro b ⟨_,⟨hf₁,hf₂⟩⟩
      rw [hf₂.symm]
      apply h
      exact ⟨lt_of_le_of_ne hf₁.1.1 hf₁.2, hf₁.1.2⟩
    · sorry


lemma lem2d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI ⟨(⊥ , ⊤) , bot_lt_top⟩ μ)
  (x : ℒ) (hx : ⊥ ≠ x)
  (w : ℒ) (hw : ⊥ ≠ w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ) (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ ∧
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ :=
  lem2d4I ℒ S ⟨(⊥ , ⊤) , bot_lt_top⟩ μ hμcvx x ⟨bot_le,le_top⟩ hx w ⟨bot_le,le_top⟩ hw hxw u ⟨bot_le, le_top⟩ t ⟨bot_le, le_top⟩ hut huxw hxwt


lemma rmk2d5a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ) :
  IsConvexI I (μmax μ)  :=
  sorry

lemma rmk2d5b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ) :
  μmax μ I = μmax (μmax μ) I :=
  sorry


lemma prop2d6main (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ ⟨(y , z) , h.right⟩ ≥ μA μ ⟨(x , z) , lt_trans h.left h.right⟩ :=
  sorry

lemma prop2d6a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z) :
  μA μ ⟨(x , z) , lt_trans h.left h.right⟩ ≥ (μA μ ⟨(x , y) , h.left⟩ ⊓ (μA μ ⟨(y , z) , h.right⟩)) :=
  sorry

lemma prop2d6b1 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.left⟩ ≥ μA μ ⟨(y , z) , h.right⟩) :
  μA μ ⟨(y , z) , h.right⟩ = μA μ ⟨(x , z) , lt_trans h.left h.right⟩ :=
  sorry

lemma prop2d6b2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.left⟩ < μA μ ⟨(y , z) , h.right⟩) :
  μA μ ⟨(x , y) , h.left⟩ ≤ μA μ ⟨(x , z) , lt_trans h.left h.right⟩ ∧
  μA μ ⟨(x , z) , lt_trans h.left h.right⟩ ≤ μA μ ⟨(y , z) , h.right⟩ :=
  sorry

lemma prop2d6c (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.left⟩ ≤ μA μ ⟨(y , z) , h.right⟩ ∨
        μA μ ⟨(x , y) , h.left⟩ ≥ μA μ ⟨(y , z) , h.right⟩ ∨
        (∃ u : S, u = μA μ ⟨(x , z) , lt_trans h.left h.right⟩)) :
  μA μ ⟨(y , z) , h.right⟩ = μA μ ⟨(x , z) , lt_trans h.left h.right⟩ ∨
  (μA μ ⟨(x , y) , h.left⟩ ≤ μA μ ⟨(x , z) , lt_trans h.left h.right⟩ ∧
   μA μ ⟨(x , z) , lt_trans h.left h.right⟩ < μA μ ⟨(y , z) , h.right⟩) :=
  sorry

lemma rmk2d7 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S] [LinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI ⟨(⊥ , ⊤) , bot_lt_top⟩ μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥ , x) , h.left⟩ > μA μ ⟨(⊥ , ⊤) , bot_lt_top⟩) :
  μA μ ⟨(x , ⊤) , h.right⟩ = μA μ ⟨(⊥ , ⊤) , bot_lt_top⟩ :=
  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y) :
  μA μ ⟨(u, x ⊔ y) , lt_sup_of_lt_left h.left⟩ ≥ μA μ ⟨(u , x) , h.left⟩ ⊓ μA μ ⟨(u , y) , h.right⟩ :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y)
  (hcpb: μA μ ⟨(u , x) , h.left⟩ ≤ μA μ ⟨(u , y) , h.right⟩ ∨
         μA μ ⟨(u , x) , h.left⟩ ≥ μA μ ⟨(u , y) , h.right⟩ ∨
         (∃ v : S, v = μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.left⟩)) :
  μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.left⟩ ≥ μA μ ⟨(u , x) , h.left⟩ ∨
  μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.left⟩ ≥ μA μ ⟨(u , x) , h.left⟩ :=
  sorry
