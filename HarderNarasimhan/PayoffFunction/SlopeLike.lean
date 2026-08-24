/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.PayoffFunction.Restrict
import HarderNarasimhan.Interval
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto

/-!
# Slope-like payoff functions

This file defines the *slope-like* axiom for a payoff function `μ`: for any chain
`x < y < z` the value on the long interval `(x, z)` is constrained between the values on the
two short intervals, as if `μ` were a slope `degree/rank` (see
`HarderNarasimhan.PayoffFunction.Slope` for that construction).

The axiom itself (`IsSlopeLike`) is a redundancy-rich conjunction of four disjunctions that
works in an arbitrary complete lattice.  Its useful reformulation is the *seesaw*
trichotomy (`IsSlopeLike.seesaw`): the three values

* `left  = μ (x, y)`,
* `total = μ (x, z)`,
* `right = μ (y, z)`

are either strictly increasing, strictly decreasing, or all equal.

## The `seesaw_*` lemmas

For each of the pairwise comparisons the trichotomy yields an equivalence with the
**left-versus-total** comparison, which we adopt as the canonical right-hand side:

* `seesaw_total_lt_right_iff` : `total < right ↔ left < total`
* `seesaw_left_lt_right_iff`  : `left < right ↔ left < total`
* `seesaw_right_lt_total_iff` : `right < total ↔ total < left`
* `seesaw_right_lt_left_iff`  : `right < left ↔ total < left`
* `seesaw_total_eq_right_iff` : `total = right ↔ left = total`
* `seesaw_left_eq_right_iff`  : `left = right ↔ left = total`

Any of the nine possible one-step implications is a `.1`/`.2` of one of these (or a
`.trans` of two).

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ] [CompleteLattice S]

/-- The *slope-like* axiom: for any chain `x < y < z`, the four disjunctions constrain the
value on `(x, z)` to sit between the values on `(x, y)` and `(y, z)` in the “seesaw” manner.
The formulation is deliberately redundancy-rich so that it is usable in a mere complete
lattice; over a linear order it is equivalent to the trichotomy `IsSlopeLike.seesaw`. -/
class IsSlopeLike (μ : PayoffFunction ℒ S) : Prop where
  /-- The four-fold seesaw condition. -/
  slopelike : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
    (μ ⟨x, y, h.1⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩) ∧
    (μ ⟨x, y, h.1⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩) ∧
    (μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨y, z, h.2⟩) ∧
    (μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨y, z, h.2⟩)

variable {μ : PayoffFunction ℒ S}

/-- Slope-likeness is stable under restriction to a subinterval. -/
instance {I : StrictIntvl ℒ} [hsl : μ.IsSlopeLike] : (μ.restrict I).IsSlopeLike :=
  ⟨fun x y z h ↦ hsl.slopelike x.val y.val z.val h⟩

/-- Slope-likeness is stable under restriction (transitional `Resμ`-keyed copy of the
`PayoffFunction.restrict` instance, so that instance search fires on `Resμ`). -/
instance [Nontrivial ℒ] [BoundedOrder ℒ] {I : StrictIntvl ℒ} [hsl : μ.IsSlopeLike] :
    (Resμ I μ).IsSlopeLike :=
  ⟨fun x y z h ↦ hsl.slopelike x.val y.val z.val h⟩

/-- The slope-like axiom is equivalent to the seesaw trichotomy: for any chain `x < y < z`
the three values `μ (x, y)`, `μ (x, z)`, `μ (y, z)` are strictly increasing, strictly
decreasing, or all equal.  This is Proposition 4.6 of [ChenJeannin]. -/
theorem isSlopeLike_iff_seesaw :
    μ.IsSlopeLike ↔ ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
      (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
      (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) := by
  constructor
  · intro sl x y z h₁ h₂
    have sl := sl.slopelike x y z ⟨h₁, h₂⟩
    by_cases h' : μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩
    · exact Or.inl ⟨h', Or.resolve_left sl.2.2.2 (not_le_of_gt h')⟩
    · by_cases h'' : μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩
      · exact Or.inr <| Or.inl ⟨h'', Or.resolve_left sl.1 (not_le_of_gt h'')⟩
      · have h₃ := not_lt_of_ge <| Or.resolve_left sl.2.1 h'
        exact Or.inr <| Or.inr ⟨(eq_of_le_of_not_lt (Or.resolve_right sl.2.2.2 h₃) h'').symm,
          eq_of_le_of_not_lt (Or.resolve_left sl.2.2.1 h'') h₃⟩
  · intro seesaw
    refine ⟨fun x y z h ↦ ?_⟩
    rcases seesaw x y z h.1 h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1.le, Or.inl h1, Or.inr h2.le, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inr h2.le, Or.inl h1, Or.inl h1.le⟩
    · exact ⟨Or.inl h1.le, Or.inr h2.ge, Or.inr h2.le, Or.inl h1.ge⟩

/-- The seesaw trichotomy for a slope-like payoff function: the three values `μ (x, y)`,
`μ (x, z)`, `μ (y, z)` are strictly increasing, strictly decreasing, or all equal. -/
lemma IsSlopeLike.seesaw (hsl : μ.IsSlopeLike) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z) :
    (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
    (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
    (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) :=
  isSlopeLike_iff_seesaw.1 hsl x y z h₁ h₂

section Seesaw

variable (hsl : μ.IsSlopeLike) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z)
include hsl

/-- Seesaw: `total < right ↔ left < total`. -/
lemma IsSlopeLike.seesaw_total_lt_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true hb ha
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_false hb.not_lt ha.not_lt

/-- Seesaw: `left < right ↔ left < total`. -/
lemma IsSlopeLike.seesaw_left_lt_right_iff :
    μ ⟨x, y, h₁⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true (ha.trans hb) ha
  · exact iff_of_false (asymm (hb.trans ha)) (asymm ha)
  · exact iff_of_false (ha.trans hb).not_lt ha.not_lt

/-- Seesaw: `right < total ↔ total < left`. -/
lemma IsSlopeLike.seesaw_right_lt_total_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_true hb ha
  · exact iff_of_false hb.not_gt ha.not_gt

/-- Seesaw: `right < left ↔ total < left`. -/
lemma IsSlopeLike.seesaw_right_lt_left_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, y, h₁⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm (ha.trans hb)) (asymm ha)
  · exact iff_of_true (hb.trans ha) ha
  · exact iff_of_false (ha.trans hb).not_gt ha.not_gt

/-- Seesaw: `total = right ↔ left = total`. -/
lemma IsSlopeLike.seesaw_total_eq_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false hb.ne ha.ne
  · exact iff_of_false hb.ne' ha.ne'
  · exact iff_of_true hb ha

/-- Seesaw: `left = right ↔ left = total`. -/
lemma IsSlopeLike.seesaw_left_eq_right_iff :
    μ ⟨x, y, h₁⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (ha.trans hb).ne ha.ne
  · exact iff_of_false (hb.trans ha).ne' ha.ne'
  · exact iff_of_true (ha.trans hb) ha

end Seesaw

end PayoffFunction

end HarderNarasimhan
