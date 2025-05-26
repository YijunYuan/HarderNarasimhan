import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (IBot : ℒ) (ITop : ℒ) (_ : IBot < ITop) (μ : ℒ × ℒ → S) : Prop := ∀ x : ℒ, ∀ y : ℒ, IBot ≤ x ∧ x ≤ ITop ∧ IBot ≤ y ∧ y ≤ ITop ∧ ¬ x ≤ y → μ (x ⊓ y,x) ≤ μ (y,x ⊔ y)


lemma lem2d4I (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (hxI : IBot < x ∧ x ≤ ITop)
  (w : ℒ) (hwI : IBot < x ∧ x ≤ ITop)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huI : IBot ≤ u ∧ u ≤ ITop)
  (t : ℒ) (huI : IBot ≤ t ∧ t ≤ ITop)
  (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μAI ℒ S μ (u , x) ≤ μmaxI ℒ S μ (x ⊓ w , x) ∧
  μmaxI ℒ S μ (x ⊓ w , x) ≤ μmaxI ℒ S μ (w , t) ∧
  μAI ℒ S μ (u , x) ≤ μAI ℒ S μ (w , t) :=
  sorry

lemma lem2d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI ⊥ ⊤ bot_lt_top μ)
  (x : ℒ) (hx : x ≠ ⊥)
  (w : ℒ) (_ : w ≠ ⊥)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ) (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μAI ℒ S μ (u , x) ≤ μmaxI ℒ S μ (x ⊓ w , x) ∧
  μmaxI ℒ S μ (x ⊓ w , x) ≤ μmaxI ℒ S μ (w , t) ∧
  μAI ℒ S μ (u , x) ≤ μAI ℒ S μ (w , t) :=
  lem2d4I ℒ S ⊥ ⊤ bot_lt_top μ hμcvx x ⟨bot_lt_iff_ne_bot.2 hx, le_top⟩ w
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
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ) :
  IsConvexI IBot ITop h (μmaxI ℒ S μ)  :=
  sorry

lemma rmk2d5b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ) :
  μmaxI ℒ S μ (IBot , ITop) = μmaxI ℒ S (μmaxI ℒ S μ) (IBot , ITop) :=
  sorry

lemma prop2d6main (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μAI ℒ S μ (y , z) ≥ μAI ℒ S μ (x , z) :=
  sorry

lemma prop2d6a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : IBot ≤ x ∧ x < y ∧ y < z ∧ z ≤ ITop) :
  μAI ℒ S μ (x , z) ≥ (μAI ℒ S μ (x , y)) ⊓ (μAI ℒ S μ (y , z)) :=
  sorry

lemma prop2d6b1 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : IBot ≤ x ∧ x < y ∧ y < z ∧ z ≤ ITop)
  (h' : μAI ℒ S μ (x , y) ≥ μAI ℒ S μ (y , z)) :
  μAI ℒ S μ (y , z) = μAI ℒ S μ (x , z) :=
  sorry

lemma prop2d6b2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : IBot ≤ x ∧ x < y ∧ y < z ∧ z ≤ ITop)
  (h' : μAI ℒ S μ (x , y) < μAI ℒ S μ (y , z)) :
  μAI ℒ S μ (x , y) ≤ μAI ℒ S μ (x , z) ∧
  μAI ℒ S μ (x , z) ≤ μAI ℒ S μ (y , z) :=
  sorry

lemma prop2d6c (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : IBot ≤ x ∧ x < y ∧ y < z ∧ z ≤ ITop)
  (h' : μAI ℒ S μ (x , y) ≤ μAI ℒ S μ (y , z) ∨
        μAI ℒ S μ (x , y) ≥ μAI ℒ S μ (y , z) ∨
        (∃ u : S, u = μAI ℒ S μ (x , z))) :
  μAI ℒ S μ (y , z) = μAI ℒ S μ (x , z) ∨
  (μAI ℒ S μ (x , y) ≤ μAI ℒ S μ (x , z) ∧
   μAI ℒ S μ (x , z) < μAI ℒ S μ (y , z)) :=
  sorry

lemma rmk2d7 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S] [LinearOrder S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI ⊥ ⊤ bot_lt_top μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μAI ℒ S μ (⊥ , x) > μAI ℒ S μ (⊥ , ⊤)) :
  μAI ℒ S μ (x , ⊤) = μAI ℒ S μ (⊥ , ⊤) :=
  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h' : IBot ≤ u ∧ u < x ∧ u < y ∧ x ≤ ITop ∧ y ≤ ITop) :
  μAI ℒ S μ (u, x ⊔ y) ≥ μAI ℒ S μ (u , x) ⊓ μAI ℒ S μ (u , y) :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI IBot ITop h μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h' : IBot ≤ u ∧ u < x ∧ u < y ∧ x ≤ ITop ∧ y ≤ ITop)
  (hcpb: μAI ℒ S μ (u , x) ≤ μAI ℒ S μ (u , y) ∨
         μAI ℒ S μ (u , x) ≥ μAI ℒ S μ (u , y) ∨
         (∃ v : S, v = μAI ℒ S μ (u , x ⊔ y))) :
  μAI ℒ S μ (u , x ⊔ y) ≥ μAI ℒ S μ (u , x) ∨
  μAI ℒ S μ (u , x ⊔ y) ≥ μAI ℒ S μ (u , x) :=
  sorry
