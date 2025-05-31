import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (I : ℒ × ℒ) (_ : I.1 < I.2) (μ : ℒ × ℒ → S) : Prop := ∀ x : ℒ, ∀ y : ℒ, InInterval I x ∧ InInterval I y ∧ ¬ x ≤ y → μ (x ⊓ y,x) ≤ μ (y,x ⊔ y)

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

lemma lem2d4I (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x) (hx : x ≠ I.1)
  (w : ℒ) (hwI : InInterval I w) (hw : w ≠ I.1)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huI : InInterval I u)
  (t : ℒ) (huI : InInterval I t)
  (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ (u , x) (u_lt_x x w u hxw huxw) ≤ μmax μ (x ⊓ w , x) (x_inf_w_lt_x x w hxw) ∧
  μmax μ (x ⊓ w , x) (x_inf_w_lt_x x w hxw) ≤ μmax μ (w , t) (w_lt_t x w t hxw hxwt) ∧
  μA μ (u , x) (u_lt_x x w u hxw huxw) ≤ μA μ (w , t) (w_lt_t x w t hxw hxwt) :=
  sorry

lemma lem2d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (⊥ , ⊤) bot_lt_top μ)
  (x : ℒ) (hx : x ≠ ⊥)
  (w : ℒ) (hw : w ≠ ⊥)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ) (hut : u < t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ (u , x) (u_lt_x x w u hxw huxw) ≤ μmax μ (x ⊓ w , x) (x_inf_w_lt_x x w hxw) ∧
  μmax μ (x ⊓ w , x) (x_inf_w_lt_x x w hxw) ≤ μmax μ (w , t) (w_lt_t x w t hxw hxwt) ∧
  μA μ (u , x) (u_lt_x x w u hxw huxw) ≤ μA μ (w , t) (w_lt_t x w t hxw hxwt) :=
  lem2d4I ℒ S (⊥ , ⊤) bot_lt_top μ hμcvx x ⟨bot_le,le_top⟩ hx w ⟨bot_le,le_top⟩ hw hxw u ⟨bot_le, le_top⟩ t ⟨bot_le, le_top⟩ hut huxw hxwt

/-
lemma rmk2d5a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ) :
  IsConvexI I hI (μmax μ)  :=
  sorry

lemma rmk2d5b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ) :
  μmax μ I = μmax (μmax μ) I :=
  sorry
-/

lemma prop2d6main (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (μ : ℒ × ℒ → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ (y , z) h.right ≥ μA μ (x , z) (lt_trans h.left h.right) :=
  sorry

lemma prop2d6a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z) :
  μA μ (x , z) (lt_trans h.left h.right) ≥ (μA μ (x , y) h.left) ⊓ (μA μ (y , z) h.right) :=
  sorry

lemma prop2d6b1 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ (x , y) h.left ≥ μA μ (y , z) h.right) :
  μA μ (y , z) h.right = μA μ (x , z) (lt_trans h.left h.right) :=
  sorry

lemma prop2d6b2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ (x , y) h.left < μA μ (y , z) h.right) :
  μA μ (x , y) h.left ≤ μA μ (x , z) (lt_trans h.left h.right) ∧
  μA μ (x , z) (lt_trans h.left h.right) ≤ μA μ (y , z) h.right :=
  sorry

lemma prop2d6c (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ (x , y) h.left ≤ μA μ (y , z) h.right ∨
        μA μ (x , y) h.left ≥ μA μ (y , z) h.right ∨
        (∃ u : S, u = μA μ (x , z) (lt_trans h.left h.right))) :
  μA μ (y , z) h.right = μA μ (x , z) (lt_trans h.left h.right) ∨
  (μA μ (x , y) h.left ≤ μA μ (x , z) (lt_trans h.left h.right) ∧
   μA μ (x , z) (lt_trans h.left h.right) < μA μ (y , z) h.right) :=
  sorry

lemma rmk2d7 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S] [LinearOrder S]
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI (⊥ , ⊤) bot_lt_top μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ (⊥ , x) h.left > μA μ (⊥ , ⊤) bot_lt_top) :
  μA μ (x , ⊤) h.right = μA μ (⊥ , ⊤) bot_lt_top :=
  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S) (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y) :
  μA μ (u, x ⊔ y) (lt_sup_of_lt_left h.left) ≥ μA μ (u , x) h.left ⊓ μA μ (u , y) h.right :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : ℒ × ℒ) (hI : I.1 < I.2)
  (μ : ℒ × ℒ → S)  (hμcvx : IsConvexI I hI μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y)
  (hcpb: μA μ (u , x) h.left ≤ μA μ (u , y) h.right ∨
         μA μ (u , x) h.left ≥ μA μ (u , y) h.right ∨
         (∃ v : S, v = μA μ (u , x ⊔ y) (lt_sup_of_lt_left h.left))) :
  μA μ (u , x ⊔ y) (lt_sup_of_lt_left h.left) ≥ μA μ (u , x) h.left ∨
  μA μ (u , x ⊔ y) (lt_sup_of_lt_left h.left) ≥ μA μ (u , x) h.left :=
  sorry

-------------------------------- `Test`
variable (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]

#check (⟨(⊥,⊤),bot_lt_top⟩ : {p : ℒ × ℒ // p.1 < p.2} )
