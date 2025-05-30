import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (I : ℒ × ℒ) (_ : I.1 < I.2) (μ : ℒ × ℒ → S) : Prop := ∀ x : ℒ, ∀ y : ℒ, I.1 ≤ x ∧ x ≤ I.2 ∧ I.1 ≤ y ∧ y ≤ I.2 ∧ ¬ x ≤ y → μ (x ⊓ y,x) ≤ μ (y,x ⊔ y)


lemma lem2d4I (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (hxI : I.1 < x ∧ x ≤ I.2)
  (w : ℒ) (hwI : I.1 < x ∧ x ≤ I.2)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huI : I.1 ≤ u ∧ u ≤ I.2)
  (t : ℒ) (huI : I.1 ≤ t ∧ t ≤ I.2)
  (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ (u , x) ≤ μmax μ (x ⊓ w , x) ∧
  μmax μ (x ⊓ w , x) ≤ μmax μ (w , t) ∧
  μA μ (u , x) ≤ μA μ (w , t) :=
  sorry

lemma lem2d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (⊥ , ⊤) bot_lt_top μ)
  (x : ℒ) (hx : x ≠ ⊥)
  (w : ℒ) (_ : w ≠ ⊥)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ) (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ (u , x) ≤ μmax μ (x ⊓ w , x) ∧
  μmax μ (x ⊓ w , x) ≤ μmax μ (w , t) ∧
  μA μ (u , x) ≤ μA μ (w , t) :=
  lem2d4I ℒ S (⊥ , ⊤) bot_lt_top μ hμcvx x ⟨bot_lt_iff_ne_bot.2 hx, le_top⟩ w
    ⟨bot_lt_iff_ne_bot.2 hx, le_top⟩ hxw u ⟨bot_le, le_top⟩ t ⟨bot_le, le_top⟩ hut huxw hxwt

lemma u_lt_x {ℒ : Type} [Lattice ℒ]
  (x : ℒ) (w : ℒ) (u : ℒ)
  (hxw : ¬ x ≤ w) (huxw : u ≤ x ⊓ w) :
  u < x :=
  lt_of_le_of_lt huxw (inf_lt_left.2 hxw)

lemma x_inf_w_lt_x {ℒ : Type} [Lattice ℒ]
  (x : ℒ) (w : ℒ)
  (hxw : ¬ x ≤ w) :
  x ⊓ w < x :=
  inf_lt_left.2 hxw

lemma w_lt_t {ℒ : Type} [Lattice ℒ]
  (x : ℒ) (w : ℒ) (t : ℒ)
  (h₁ : ¬ x ≤ w) (h₂ : x ⊔ w ≤ t) :
  w < t :=
  lt_iff_le_and_ne.2
    ⟨ le_trans le_sup_right h₂,
      fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) h₁ (sup_le_iff.1 h₂).left⟩


lemma rmk2d5a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ) :
  IsConvexI (I.1 , I.2) h (μmax μ)  :=
  sorry

lemma rmk2d5b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ) :
  μmax μ (I.1 , I.2) = μmax (μmax μ) (I.1 , I.2) :=
  sorry

lemma prop2d6main (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ (y , z) ≥ μA μ (x , z) :=
  sorry

lemma prop2d6a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : I.1 ≤ x ∧ x < y ∧ y < z ∧ z ≤ I.2) :
  μA μ (x , z) ≥ (μA μ (x , y)) ⊓ (μA μ (y , z)) :=
  sorry

lemma prop2d6b1 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : I.1 ≤ x ∧ x < y ∧ y < z ∧ z ≤ I.2)
  (h' : μA μ (x , y) ≥ μA μ (y , z)) :
  μA μ (y , z) = μA μ (x , z) :=
  sorry

lemma prop2d6b2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : I.1 ≤ x ∧ x < y ∧ y < z ∧ z ≤ I.2)
  (h' : μA μ (x , y) < μA μ (y , z)) :
  μA μ (x , y) ≤ μA μ (x , z) ∧
  μA μ (x , z) ≤ μA μ (y , z) :=
  sorry

lemma prop2d6c (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : I.1 ≤ x ∧ x < y ∧ y < z ∧ z ≤ I.2)
  (h' : μA μ (x , y) ≤ μA μ (y , z) ∨
        μA μ (x , y) ≥ μA μ (y , z) ∨
        (∃ u : S, u = μA μ (x , z))) :
  μA μ (y , z) = μA μ (x , z) ∨
  (μA μ (x , y) ≤ μA μ (x , z) ∧
   μA μ (x , z) < μA μ (y , z)) :=
  sorry

lemma rmk2d7 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S] [LinearOrder S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (⊥ , ⊤) bot_lt_top μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ (⊥ , x) > μA μ (⊥ , ⊤)) :
  μA μ (x , ⊤) = μA μ (⊥ , ⊤) :=
  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h' : I.1 ≤ u ∧ u < x ∧ u < y ∧ x ≤ I.2 ∧ y ≤ I.2) :
  μA μ (u, x ⊔ y) ≥ μA μ (u , x) ⊓ μA μ (u , y) :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (h : I.1 < I.2)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI (I.1 , I.2) h μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h' : I.1 ≤ u ∧ u < x ∧ u < y ∧ x ≤ I.2 ∧ y ≤ I.2)
  (hcpb: μA μ (u , x) ≤ μA μ (u , y) ∨
         μA μ (u , x) ≥ μA μ (u , y) ∨
         (∃ v : S, v = μA μ (u , x ⊔ y))) :
  μA μ (u , x ⊔ y) ≥ μA μ (u , x) ∨
  μA μ (u , x ⊔ y) ≥ μA μ (u , x) :=
  sorry
