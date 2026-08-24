/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Completion
import HarderNarasimhan.Interval

/-!
This file defines the “slope-like” axioms for an interval-indexed function `μ`.

The guiding intuition (from Harder–Narasimhan style theories) is that `μ(x,z)` behaves like a slope:
for any `x<y<z`, the value on the long interval is constrained relative to the two short intervals.
The axiom is formulated purely order-theoretically so that it can be instantiated in a variety of
settings.

In addition, this file introduces a small amount of ordered linear-algebra infrastructure used later
to build examples of slope-like functions by taking quotients `d/r` (encoded as `μQuotient`).

Main API:
- `SlopeLike μ`: the slope-like condition as a typeclass `Prop`.
- `μQuotient r d`: a construction producing values in the Dedekind–MacNeille completion
  (`DedekindCut` from mathlib) to handle division by zero.
- An instance showing slope-likeness is stable under restriction to an interval via `Resμ`.
-/

namespace HarderNarasimhan

/--
Slope-like axiom for an interval-indexed function `μ`.

For any triple `x<y<z`, the four conjuncts express a “seesaw” behavior: the value on the long
interval sits between the values on the two short intervals, allowing weak/strict inequalities in a
way that is robust in a mere `CompleteLattice`.

API design:
- Implemented as a typeclass `Prop` with a single field `slopelike` so it can be passed implicitly.
- The statement is deliberately redundancy-rich (four conjuncts) to support rewriting without linear
  order.
-/
class SlopeLike {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : StrictIntvl ℒ → S) : Prop where
  slopelike : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
(
  μ ⟨x, y, h.1⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨x, y, h.1⟩ < μ ⟨x, z, lt_trans h.1 h.2⟩ ∨ μ ⟨y, z, h.2⟩ ≤ μ ⟨x, z, lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨y, z, h.2⟩
) ∧ (
  μ ⟨x, z, lt_trans h.1 h.2⟩ ≤ μ ⟨x, y, h.1⟩ ∨ μ ⟨x, z, lt_trans h.1 h.2⟩ < μ ⟨y, z, h.2⟩
)


/--
Construct a “quotient slope” from a nonnegative real-valued rank `r` and a vector-valued degree `d`.

The target is `DedekindCut V` (the Dedekind–MacNeille completion) to accommodate the case
`r z = 0`:
- if `r z > 0`, we return the scaled vector `(r z)⁻¹ • d z` as a principal cut;
- otherwise we return `⊤`.

API note: this design avoids partial functions/division-by-zero and allows the resulting `μ` to live
in a complete lattice (the completion), which is compatible with `sSup`/`sInf`-based constructions
elsewhere.
-/
noncomputable def μQuotient {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
[PosSMulStrictMono ℝ V]
(r : StrictIntvl ℒ → NNReal)
(d : StrictIntvl ℒ → V) :
StrictIntvl ℒ → DedekindCut V :=
  fun z ↦ if _ : r z > 0 then .principal ((r z)⁻¹ • d z) else ⊤


/--
Slope-likeness is stable under restriction to a subinterval.

If `μ` is slope-like on `ℒ`, then the restricted function `Resμ z μ` is slope-like on `↥z`.
This is proved by unpacking the restriction and applying `SlopeLike.slopelike` to underlying
elements.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : StrictIntvl ℒ → S} [hsl : SlopeLike μ]
{z : StrictIntvl ℒ} : SlopeLike (Resμ z μ)
:= { slopelike := fun x y z h ↦ hsl.slopelike x.val y.val z.val h }

end HarderNarasimhan
