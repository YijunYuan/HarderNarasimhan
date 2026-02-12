import HarderNarasimhan.Basic
import HarderNarasimhan.Interval

namespace HarderNarasimhan

class Convex {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  convex : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩

class ConvexI {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  convex : ∀ x y : ℒ, InIntvl I x → InIntvl I y → (h : ¬ x ≤ y) →
    μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩

lemma Convex_of_Convex_large {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(I₁ : {p : ℒ × ℒ // p.1 < p.2})
(I₂ : {p : ℒ × ℒ // p.1 < p.2})
(hI : I₁.val.1 ≤ I₂.val.1 ∧ I₂.val.2 ≤ I₁.val.2)
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
ConvexI I₁ μ → ConvexI I₂ μ :=
  fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex x y ⟨le_trans hI.1 hx.1,
    le_trans hx.2 hI.2⟩ ⟨le_trans hI.1 hy.1, le_trans hy.2 hI.2⟩ hxy }

end HarderNarasimhan
