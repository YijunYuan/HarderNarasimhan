import HarderNarasimhan.Basic

section

variable {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
variable {S : Type} [CompleteLattice S]

def IsConvexI (I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℒ, ∀ y : ℒ, InIntvl I x → InIntvl I y → (h : ¬ x ≤ y) → μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩

lemma Convex_of_Convex_large
(I₁ : {p : ℒ × ℒ // p.1 < p.2})
(I₂ : {p : ℒ × ℒ // p.1 < p.2})
(hI : I₁.val.1 ≤ I₂.val.1 ∧ I₂.val.2 ≤ I₁.val.2)
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
IsConvexI I₁ μ → IsConvexI I₂ μ := fun hμcvx₁ x y hxI hyI hxy ↦ hμcvx₁ x y ⟨le_trans hI.1 hxI.1, le_trans hxI.2 hI.2⟩ ⟨le_trans hI.1 hyI.1, le_trans hyI.2 hI.2⟩ hxy

def IsConvex
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
IsConvexI TotIntvl μ

end
