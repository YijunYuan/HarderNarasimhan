/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.SlopeLike.Impl

/-!
This file exposes the main user-facing results of the `SlopeLike` module.

The `SlopeLike` axiom in
[HarderNarasimhan/SlopeLike/Defs.lean](HarderNarasimhan/SlopeLike/Defs.lean) is given
as four conjunctive inequalities that work in a general complete lattice. The implementation file
`SlopeLike/Impl.lean` proves an equivalent “seesaw” formulation as a disjunction of three patterns.

This file:
- re-exports that equivalence as `seesaw`,
- provides a convenient theorem `SlopeLike_of_μQuotient` constructing slope-like functions from the
  quotient construction `μQuotient`,
- derives a more implication-oriented helper lemma `seesaw'` for common proof patterns.
-/

namespace HarderNarasimhan

/--
Public seesaw characterization of `SlopeLike μ`.

This is a direct re-export of `impl.prop4d6`. It states that for every triple `x<y<z`, the three
values `μ(x,y)`, `μ(x,z)`, `μ(y,z)` are either strictly increasing, strictly decreasing, or all
equal.

API note: this form is often significantly easier to use in proofs than the original four-conjunct
definition.
-/
lemma seesaw {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
------------
SlopeLike μ ↔
∀ (x y z : ℒ), (h : x < y ∧ y < z) → (
  μ ⟨x, y, h.1⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩ ∧ μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨y, z, h.2⟩
  ∨
  μ ⟨x, y, h.1⟩ > μ ⟨x, z, lt_trans h.1 h.2⟩ ∧ μ ⟨x, z, lt_trans h.1 h.2⟩ > μ ⟨y, z, h.2⟩
  ∨
  μ ⟨x, y, h.1⟩ = μ ⟨x, z, lt_trans h.1 h.2⟩ ∧ μ ⟨x, z, lt_trans h.1 h.2⟩ = μ ⟨y, z, h.2⟩
)
------------
:= impl.prop4d6 μ


/--
Construct a slope-like function from the quotient construction `μQuotient`.

This theorem packages `impl.prop4d8` as a user-facing API:
given additivity of rank `r` and degree `d` on composable intervals and a positivity condition when
`r=0`, the induced `μQuotient r d` is slope-like.
-/
theorem SlopeLike_of_μQuotient {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
[PosSMulStrictMono ℝ V] [Nontrivial V]
(r : Intvl ℒ → NNReal)
(d : Intvl ℒ → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
  d ⟨x, z, lt_trans h.1 h.2⟩ = d ⟨x, y, h.1⟩ + d ⟨y, z, h.2⟩ ∧
  r ⟨x, z, lt_trans h.1 h.2⟩ = r ⟨x, y, h.1⟩ + r ⟨y, z, h.2⟩)
(h₂ : ∀ (x y : ℒ), (h : x < y) → r ⟨x, y, h⟩ = 0 → d ⟨x, y, h⟩ > 0) :
------------
 SlopeLike (μQuotient r d)
------------
:= impl.prop4d8 r d h₁ h₂


/--
An implication-style reformulation of the seesaw behavior.

Assuming `SlopeLike μ`, this lemma provides several “if one comparison holds, then the other two
follow” statements, separately for the increasing, decreasing, and constant cases.

API note: this is tailored for forward reasoning in proofs where one inequality is known and the
remaining relations need to be derived.
-/
lemma seesaw' {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
------------
SlopeLike μ → ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
(
  (
    μ ⟨x, y,h.1⟩ < μ ⟨x, z,lt_trans h.1 h.2⟩ →
      μ ⟨x, y,h.1⟩ < μ ⟨y, z,h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ < μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, y,h.1⟩ < μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ < μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ < μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, z,lt_trans h.1 h.2⟩ < μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ < μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, y,h.1⟩ < μ ⟨y, z,h.2⟩
  )
) ∧ (
  (
    μ ⟨x, y,h.1⟩ > μ ⟨x, z,lt_trans h.1 h.2⟩ →
      μ ⟨x, y,h.1⟩ > μ ⟨y, z,h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ > μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, y,h.1⟩ > μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ > μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ > μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, z,lt_trans h.1 h.2⟩ > μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ > μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, y,h.1⟩ > μ ⟨y, z,h.2⟩
  )
) ∧ (
  (
    μ ⟨x, y,h.1⟩ = μ ⟨x, z,lt_trans h.1 h.2⟩ →
      μ ⟨x, y,h.1⟩ = μ ⟨y, z,h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ = μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, y,h.1⟩ = μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ = μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, z,lt_trans h.1 h.2⟩ = μ ⟨y, z,h.2⟩
  ) ∧ (
    μ ⟨x, z,lt_trans h.1 h.2⟩ = μ ⟨y, z,h.2⟩ →
      μ ⟨x, y,h.1⟩ = μ ⟨x, z,lt_trans h.1 h.2⟩ ∧ μ ⟨x, y,h.1⟩ = μ ⟨y, z,h.2⟩
  )
) := by
  intro hsl x y z h
  rcases (seesaw μ).1 hsl x y z h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨fun _ ↦ ⟨h1.trans h2, h2⟩, fun _ ↦ ⟨h1, h2⟩, fun _ ↦ ⟨h1, h1.trans h2⟩⟩,
      ⟨fun h' ↦ absurd h' h1.asymm, fun h' ↦ absurd h' (h1.trans h2).asymm,
        fun h' ↦ absurd h' h2.asymm⟩,
      ⟨fun h' ↦ absurd h' h1.ne, fun h' ↦ absurd h' (h1.trans h2).ne,
        fun h' ↦ absurd h' h2.ne⟩⟩
  · exact ⟨⟨fun h' ↦ absurd h' h1.asymm, fun h' ↦ absurd h' (h2.trans h1).asymm,
        fun h' ↦ absurd h' h2.asymm⟩,
      ⟨fun _ ↦ ⟨h2.trans h1, h2⟩, fun _ ↦ ⟨h1, h2⟩, fun _ ↦ ⟨h1, h2.trans h1⟩⟩,
      ⟨fun h' ↦ absurd h' h1.ne', fun h' ↦ absurd h' (h2.trans h1).ne',
        fun h' ↦ absurd h' h2.ne'⟩⟩
  · exact ⟨⟨fun h' ↦ absurd h' h1.not_lt, fun h' ↦ absurd h' (h1.trans h2).not_lt,
        fun h' ↦ absurd h' h2.not_lt⟩,
      ⟨fun h' ↦ absurd h' h1.not_gt, fun h' ↦ absurd h' (h1.trans h2).not_gt,
        fun h' ↦ absurd h' h2.not_gt⟩,
      ⟨fun _ ↦ ⟨h1.trans h2, h2⟩, fun _ ↦ ⟨h1, h2⟩, fun _ ↦ ⟨h1, h1.trans h2⟩⟩⟩

end HarderNarasimhan
