import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℒ, ∀ y : ℒ, InInterval I x → InInterval I y → (h : ¬ x ≤ y) → μ ⟨(x ⊓ y , x) , inf_lt_left.2 h⟩ ≤ μ ⟨(y,x ⊔ y) , right_lt_sup.2 h⟩


lemma lem2d4₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (w : ℒ) (hxw : ¬ x ≤ w)
  (u : ℒ) (huxw : u ≤ x ⊓ w) :
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ := by
  have h1 : μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ := by
    apply sInf_le_sInf
    intro t ht
    rcases ht with ⟨a, ha, _⟩
    use a , ⟨⟨le_trans huxw ha.1.1,ha.1.2⟩, ha.2⟩
  have h2 : μA μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ := by
    apply sInf_le
    use x ⊓ w, ⟨⟨le_rfl,le_of_lt (inf_lt_left.2 hxw)⟩ ,ne_of_lt (inf_lt_left.2 hxw)⟩
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
  μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by
    have h : ∀ b : ℒ, (h' : x ⊓ w < b ∧ b ≤ x) →
        μ ⟨(x ⊓ w , b) , h'.1⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ := by
      intro b hb
      have hh : x ⊓ w = b ⊓ w := by
        apply le_antisymm
        · nth_rw 1 [← inf_idem w]
          rw [← inf_assoc]
          exact inf_le_inf_right w <| le_of_lt hb.1
        · exact inf_le_inf_right w hb.2
      simp [hh]
      have hbI : InInterval I b := ⟨le_of_lt (lt_of_le_of_lt (le_inf hxI.1 hwI.1) hb.1), le_trans hb.2 hxI.2⟩
      have hbnlew : ¬ b ≤ w := inf_lt_left.mp
        ((congrArg (fun _a ↦ _a < b) (hh.symm)) ▸ hb.1)
      have hfinal : μ ⟨(w, b ⊔ w), IsConvexI._proof_2 b w hbnlew⟩ ≤ μmax μ ⟨(w, t), gt_of_ge_of_gt hxwt (right_lt_sup.mpr hxw)⟩ := by
        apply le_sSup
        use b ⊔ w , ⟨⟨le_sup_right,le_trans (sup_le_sup_right hb.2 w) hxwt⟩,(mt right_eq_sup.1) <| inf_lt_left.1 <| lt_of_eq_of_lt hh.symm hb.1⟩
      apply le_trans (hμcvx b w hbI hwI hbnlew) hfinal
    apply sSup_le
    rintro b ⟨_,⟨hf₁,hf₂⟩⟩
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
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w , x ⊔ w) , right_lt_sup.2 hxw⟩ := by
  apply le_sInf
  rintro imy ⟨y,⟨hy₁,hy₂⟩⟩
  rw [← hy₂]
  have h₁ : ¬ x ≤ y := by
    by_contra h
    exact lt_irrefl (x ⊔ w) (lt_of_le_of_lt (sup_le_sup_right h w) (lt_of_eq_of_lt (sup_eq_left.2 hy₁.1.1) (lt_of_le_of_ne hy₁.1.2 hy₁.2)))
  apply le_trans
  · apply lem2d4₁ μ x y h₁ u (le_trans huxw <| inf_le_inf_left x hy₁.1.1)
  · apply lem2d4₂I I μ hμcvx x hxI y ⟨le_trans hwI.1 hy₁.1.1,le_trans hy₁.1.2 <| sup_le hxI.2 hwI.2⟩ h₁ (x ⊔ w) (sup_le le_sup_left hy₁.1.2)


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
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w , x) , inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(w , t) , gt_of_ge_of_gt hxwt <| right_lt_sup.2 hxw⟩ ∧
  μA μ ⟨(u , x) , lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w , x ⊔ w) , right_lt_sup.2 hxw⟩ :=
  ⟨lem2d4₁ μ x w hxw u huxw,⟨lem2d4₂I I μ hμcvx x hxI w hwI hxw t hxwt,lem2d4₃I I μ hμcvx x hxI w hwI hxw u huxw⟩⟩


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
  μA μ ⟨(y , z) , h.2⟩ ≥ μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ :=
  sorry

lemma prop2d6a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z) :
  μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ ≥ (μA μ ⟨(x , y) , h.1⟩ ⊓ (μA μ ⟨(y , z) , h.2⟩)) :=
  sorry

lemma prop2d6b1 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.1⟩ ≥ μA μ ⟨(y , z) , h.2⟩) :
  μA μ ⟨(y , z) , h.2⟩ = μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ :=
  sorry

lemma prop2d6b2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.1⟩ < μA μ ⟨(y , z) , h.2⟩) :
  μA μ ⟨(x , y) , h.1⟩ ≤ μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ ∧
  μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y , z) , h.2⟩ :=
  sorry

lemma prop2d6c (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (z : ℒ) (hzI : InInterval I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x , y) , h.1⟩ ≤ μA μ ⟨(y , z) , h.2⟩ ∨
        μA μ ⟨(x , y) , h.1⟩ ≥ μA μ ⟨(y , z) , h.2⟩ ∨
        (∃ u : S, u = μA μ ⟨(x , z) , lt_trans h.1 h.2⟩)) :
  μA μ ⟨(y , z) , h.2⟩ = μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ ∨
  (μA μ ⟨(x , y) , h.1⟩ ≤ μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ ∧
   μA μ ⟨(x , z) , lt_trans h.1 h.2⟩ < μA μ ⟨(y , z) , h.2⟩) :=
  sorry

lemma rmk2d7 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S] [LinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI ⟨(⊥ , ⊤) , bot_lt_top⟩ μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥ , x) , h.1⟩ > μA μ ⟨(⊥ , ⊤) , bot_lt_top⟩) :
  μA μ ⟨(x , ⊤) , h.2⟩ = μA μ ⟨(⊥ , ⊤) , bot_lt_top⟩ :=
  sorry

lemma prop2d8a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y) :
  μA μ ⟨(u, x ⊔ y) , lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u , x) , h.1⟩ ⊓ μA μ ⟨(u , y) , h.2⟩ :=
  sorry

lemma prop2d8b (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  (S : Type) [CompleteLattice S]
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)  (hμcvx : IsConvexI I μ)
  (x : ℒ) (hxI : InInterval I x)
  (y : ℒ) (hyI : InInterval I y)
  (u : ℒ) (huI : InInterval I u)
  (h : u < x ∧ u < y)
  (hcpb: μA μ ⟨(u , x) , h.1⟩ ≤ μA μ ⟨(u , y) , h.2⟩ ∨
         μA μ ⟨(u , x) , h.1⟩ ≥ μA μ ⟨(u , y) , h.2⟩ ∨
         (∃ v : S, v = μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.1⟩)) :
  μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u , x) , h.1⟩ ∨
  μA μ ⟨(u , x ⊔ y) , lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u , x) , h.1⟩ :=
  sorry
