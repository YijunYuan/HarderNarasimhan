import HarderNarasimhan.Basic
import HarderNarasimhan.Interval

namespace HarderNarasimhan

class ConvexI {ℒ : Type} [Lattice ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  convex : ∀ x : ℒ, ∀ y : ℒ, InIntvl I x → InIntvl I y → (h : ¬ x ≤ y) → μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩

abbrev Convex {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) := ConvexI TotIntvl μ

theorem Convex_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Convex μ ↔
∀ x : ℒ, ∀ y : ℒ, (h : ¬ x ≤ y) → μ ⟨(x ⊓ y, x), inf_lt_left.2 h⟩ ≤ μ ⟨(y, x ⊔ y), right_lt_sup.2 h⟩ := by
  constructor
  · intro h
    exact fun x y hxy ↦ h.convex x y (in_TotIntvl _) (in_TotIntvl _) hxy
  · intro h
    exact { convex := fun x y hx hy hxy ↦ h x y hxy }

theorem ConvexI_iff_Convex_res {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2}) (μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
ConvexI I μ ↔ Convex (Resμ I μ) := by
  constructor
  · exact fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex x y x.prop y.prop hxy }
  · exact fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex ⟨x,hx⟩ ⟨y,hy⟩ (in_TotIntvl _) (in_TotIntvl _) hxy }

lemma Convex_of_Convex_large {ℒ : Type} [Lattice ℒ]
{S : Type} [CompleteLattice S]
(I₁ : {p : ℒ × ℒ // p.1 < p.2})
(I₂ : {p : ℒ × ℒ // p.1 < p.2})
(hI : I₁.val.1 ≤ I₂.val.1 ∧ I₂.val.2 ≤ I₁.val.2)
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
ConvexI I₁ μ → ConvexI I₂ μ := fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex x y ⟨le_trans hI.1 hx.1, le_trans hx.2 hI.2⟩ ⟨le_trans hI.1 hy.1, le_trans hy.2 hI.2⟩ hxy }

end HarderNarasimhan
