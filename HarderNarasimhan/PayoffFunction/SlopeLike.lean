/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Tauto

/-!
# Slope-like payoff functions

A payoff function is slope-like if it satisfies the seesaw property: for `x < y < z`, the
three values `μ (x, y)`, `μ (x, z)` and `μ (y, z)` are strictly increasing, strictly decreasing,
or all equal. Slopes obtained by dividing an additive degree by an additive nonnegative rank
satisfy this property when the degree is positive on intervals of rank zero; see
`HarderNarasimhan/PayoffFunction/Slope.lean`.

## Main declarations

* `HarderNarasimhan.PayoffFunction.IsSlopeLike`: the slope-like condition, expressed as four
  alternatives between inequalities.
* `HarderNarasimhan.PayoffFunction.isSlopeLike_iff_seesaw`: equivalence with the seesaw
  trichotomy, for payoffs in a complete lattice.

The comparison lemmas, such as
`HarderNarasimhan.PayoffFunction.IsSlopeLike.seesaw_total_lt_right_iff`, express comparisons
between the three values in terms of the comparison between `μ (x, y)` and `μ (x, z)`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ] [CompleteLattice S]

/-- A payoff function is slope-like if, for `x < y < z`, the payoffs on `(x, y)`, `(x, z)`
and `(y, z)` satisfy the seesaw condition.

The four alternatives below are equivalent to these three values being strictly increasing,
strictly decreasing, or all equal; see
`HarderNarasimhan.PayoffFunction.isSlopeLike_iff_seesaw`. -/
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

/-- The slope-like axiom is equivalent to the seesaw trichotomy: for any chain `x < y < z`
the three values `μ (x, y)`, `μ (x, z)`, `μ (y, z)` are strictly increasing, strictly
decreasing, or all equal. -/
theorem isSlopeLike_iff_seesaw :
    μ.IsSlopeLike ↔ ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
      (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
      (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) := by
  constructor
  · intro sl x y z h₁ h₂
    have sl := sl.slopelike x y z ⟨h₁, h₂⟩
    by_cases h' : μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩
    · exact Or.inl ⟨h', sl.2.2.2.resolve_left (not_le_of_gt h')⟩
    · by_cases h'' : μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩
      · exact Or.inr <| Or.inl ⟨h'', sl.1.resolve_left (not_le_of_gt h'')⟩
      · have h₃ := not_lt_of_ge <| sl.2.1.resolve_left h'
        exact Or.inr <| Or.inr ⟨(eq_of_le_of_not_lt (sl.2.2.2.resolve_right h₃) h'').symm,
          eq_of_le_of_not_lt (sl.2.2.1.resolve_left h'') h₃⟩
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

/-- The total payoff is less than the right payoff iff the left payoff is less than the
total payoff. -/
lemma IsSlopeLike.seesaw_total_lt_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true hb ha
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_false hb.not_lt ha.not_lt

/-- The left payoff is less than the right payoff iff it is less than the total payoff. -/
lemma IsSlopeLike.seesaw_left_lt_right_iff :
    μ ⟨x, y, h₁⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true (ha.trans hb) ha
  · exact iff_of_false (asymm (hb.trans ha)) (asymm ha)
  · exact iff_of_false (ha.trans hb).not_lt ha.not_lt

/-- The right payoff is less than the total payoff iff the total payoff is less than the
left payoff. -/
lemma IsSlopeLike.seesaw_right_lt_total_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_true hb ha
  · exact iff_of_false hb.not_gt ha.not_gt

/-- The right payoff is less than the left payoff iff the total payoff is less than the
left payoff. -/
lemma IsSlopeLike.seesaw_right_lt_left_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, y, h₁⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm (ha.trans hb)) (asymm ha)
  · exact iff_of_true (hb.trans ha) ha
  · exact iff_of_false (ha.trans hb).not_gt ha.not_gt

/-- The total and right payoffs are equal iff the left and total payoffs are equal. -/
lemma IsSlopeLike.seesaw_total_eq_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false hb.ne ha.ne
  · exact iff_of_false hb.ne' ha.ne'
  · exact iff_of_true hb ha

/-- The left and right payoffs are equal iff the left and total payoffs are equal. -/
lemma IsSlopeLike.seesaw_left_eq_right_iff :
    μ ⟨x, y, h₁⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases hsl.seesaw h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (ha.trans hb).ne ha.ne
  · exact iff_of_false (hb.trans ha).ne' ha.ne'
  · exact iff_of_true (ha.trans hb) ha

end Seesaw

end PayoffFunction

end HarderNarasimhan
