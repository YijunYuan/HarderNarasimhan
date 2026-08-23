/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic
import HarderNarasimhan.Interval

/-!
This file introduces the convexity assumptions on an interval-indexed function `μ`.

The convexity axioms are formulated in a lattice `ℒ` and compare the value of `μ` on two “opposite”
subintervals derived from a non-comparable pair `x,y`.

API overview:
- `Convex μ` is a global convexity condition, stated for all `x,y : ℒ`.
- `ConvexI I μ` is the same condition localized to a fixed strict interval `I` via the predicate
  ` ∈ `.
- `Convex_of_Convex_large` is a monotonicity lemma: convexity on a larger interval implies convexity
  on a smaller subinterval.

Design note: convexity is expressed as a typeclass `Prop` so that it can be passed implicitly and
  used by instance inference in later modules.
-/

namespace HarderNarasimhan

/--
Global convexity condition for `μ` on a lattice `ℒ`.

Given `x,y` with `¬ x ≤ y` (so `x` is not below `y`), the inequality compares two intervals:
- the “lower-left” interval `(x ⊓ y, x)` and
- the “upper-right” interval `(y, x ⊔ y)`.

This is a lattice-theoretic analogue of discrete convexity/supermodularity-type inequalities.
As an API, the class exposes a single field `convex` that can be invoked as `h.convex x y hxy`.
-/
class Convex {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) : Prop where
  convex : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/--
Interval-localized convexity condition.

This is the same inequality as `Convex`, but only required for `x,y` that lie in a fixed interval
`I`. This form is useful when doing induction/recursion on subintervals and when restricting `μ`.
-/
class ConvexI {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(I : Intvl ℒ)
(μ : Intvl ℒ → S) : Prop where
  convex : ∀ x y : ℒ, x ∈ I → y ∈ I → (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/--
Monotonicity of interval-local convexity under shrinking the interval.

If `I₂` is contained in `I₁` (written as endpoint inequalities `I₁.left ≤ I₂.left` and
`I₂.right ≤ I₁.right`), then any `x,y ∈ I₂` are also in `I₁`, so convexity on `I₁` implies convexity
on `I₂`.

API note: the lemma is phrased as a function `ConvexI I₁ μ → ConvexI I₂ μ` so it can be used with
`exact`.
-/
lemma Convex_of_Convex_large {ℒ : Type*} [Lattice ℒ]
{S : Type*} [CompleteLattice S]
(I₁ : Intvl ℒ)
(I₂ : Intvl ℒ)
(hI : I₁.left ≤ I₂.left ∧ I₂.right ≤ I₁.right)
(μ : Intvl ℒ → S) :
ConvexI I₁ μ → ConvexI I₂ μ :=
  fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex x y ⟨le_trans hI.1 hx.1,
    le_trans hx.2 hI.2⟩ ⟨le_trans hI.1 hy.1, le_trans hy.2 hI.2⟩ hxy }

end HarderNarasimhan
