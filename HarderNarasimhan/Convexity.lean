import HarderNarasimhan.Basic

def IsConvexI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (IBot : ℒ) (ITop : ℒ) (_ : IBot < ITop) (μ : ℒ × ℒ → S) : Prop := ∀ x : ℒ, ∀ y : ℒ, IBot ≤ x ∧ x ≤ ITop ∧ IBot ≤ y ∧ y ≤ ITop ∧ ¬ x ≤ y → μ (x ⊓ y,x) ≤ μ (y,x ⊔ y)

--lemma lem2d4IH₃ {ℒ : Type} [Lattice ℒ] (x : ℒ) (w : ℒ) (t : ℒ) (h₁ : ¬ x ≤ w) (h₂ : x ⊔ w ≤ t) : w < t := lt_iff_le_and_ne.2
--  ⟨ le_trans le_sup_right h₂,
--    fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) h₁ (sup_le_iff.1 h₂).left⟩

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
(μAI ℒ S μ u x (lt_of_le_of_lt huxw (inf_lt_left.2 hxw))) ≤ μmaxI ℒ S μ (x ⊓ w) x  (inf_lt_left.2 hxw) ∧
μmaxI ℒ S μ (x ⊓ w) x (inf_lt_left.2 hxw) ≤ μmaxI ℒ S μ w t (lt_iff_le_and_ne.2
  ⟨ le_trans le_sup_right hxwt,
    fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) hxw (sup_le_iff.1 hxwt).left⟩) ∧
(μAI ℒ S μ u x (lt_of_le_of_lt huxw (inf_lt_left.2 hxw))) ≤ μAI ℒ S μ w t (lt_iff_le_and_ne.2
  ⟨ le_trans le_sup_right hxwt,
    fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) hxw (sup_le_iff.1 hxwt).left⟩)
:= sorry

lemma lem2d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : ℒ × ℒ → S) (hμcvx : IsConvexI ⊥ ⊤ bot_lt_top μ)
(x : ℒ) (hx : x ≠ ⊥)
(w : ℒ) (_ : w ≠ ⊥)
(hxw : ¬ x ≤ w)
(u : ℒ)
(t : ℒ)
(hut : u < t)
(huxw : u ≤ x ⊓ w)
(hxwt : x ⊔ w ≤ t) :
(μAI ℒ S μ u x (lt_of_le_of_lt huxw (inf_lt_left.2 hxw))) ≤ μmaxI ℒ S μ (x ⊓ w) x  (inf_lt_left.2 hxw) ∧
μmaxI ℒ S μ (x ⊓ w) x (inf_lt_left.2 hxw) ≤ μmaxI ℒ S μ w t (lt_iff_le_and_ne.2
  ⟨ le_trans le_sup_right hxwt,
    fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) hxw (sup_le_iff.1 hxwt).left⟩) ∧
(μAI ℒ S μ u x (lt_of_le_of_lt huxw (inf_lt_left.2 hxw))) ≤ μAI ℒ S μ w t (lt_iff_le_and_ne.2
  ⟨ le_trans le_sup_right hxwt,
    fun a ↦ Eq.mp (congrArg (fun _a ↦ ¬x ≤ _a) a) hxw (sup_le_iff.1 hxwt).left⟩)
:= lem2d4I ℒ S ⊥ ⊤ bot_lt_top μ hμcvx x ⟨bot_lt_iff_ne_bot.2 hx, le_top⟩ w
  ⟨bot_lt_iff_ne_bot.2 hx, le_top⟩ hxw u ⟨bot_le, le_top⟩ t ⟨bot_le, le_top⟩ hut huxw hxwt

--lemma rmk2d5a (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (IBot : ℒ) (ITop : ℒ) (h : IBot < ITop)
--(μ : ℒ × ℒ → S) (hμcvx : IsConvexI IBot ITop h μ) : IsConvexI IBot ITop h () := sorry
