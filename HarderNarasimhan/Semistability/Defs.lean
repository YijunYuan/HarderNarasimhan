/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Interval

/-!
This file defines (semi)stability notions for the Harder–Narasimhan game formalization.

The key invariant is the value `μA μ I` from `Basic.lean`, which is an infimum of “optimized” values
of `μ` over subintervals. Semistability is formulated by comparing `μA μ (⊥,x)` to the global value
`μA μ (⊥,⊤)`.

API overview:
- `μA_DescendingChainCondition μ` is a DCC-type hypothesis ensuring the `μA`-values stabilize along
  strict descending chains; it is used to prove existence of stable objects.
- `S₁I` and `S₂I` are auxiliary predicates describing a “best” choice of breakpoint `x` inside an
  interval.
- `StI μ I` is the set of such breakpoints; `St μ` specializes to the total interval.
- `semistableI μ I` states that the right endpoint of `I` lies in `StI μ I`.
- `Semistable μ` and `Stable μ` are global classes encoding semistability/stability.

Design notes:
We keep the main user-facing concepts as typeclasses (`Semistable`, `Stable`) so that later results
can assume them implicitly. The internal selection predicates (`S₁I`, `S₂I`, `StI`) are plain
definitions, as they are primarily implementation tools.
-/

namespace HarderNarasimhan

/-
Descending chain condition for `μA`.

Given a fixed left endpoint `a` and a strictly descending chain `f : ℕ → ℒ` with all terms above
`a`, the sequence `μA μ (a, f n)` cannot decrease strictly forever. Concretely, there exists `N`
such that `μA μ (a, f N) < μA μ (a, f (N+1))` fails.

API note: formulated as a class so it can be assumed as an implicit hypothesis in existence
theorems.
-/
class μA_DescendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  μ_dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μA μ ⟨(a, f N), h₁ N⟩ < μA μ ⟨(a, f <| N + 1), h₁ <| N + 1⟩


/-
Auxiliary predicate `S₁I` (“no strictly better choice”).

For an interval `I` and a candidate breakpoint `x` inside it (with `x ≠ I.left`), `S₁I μ I x` says:
for any other candidate `y` inside `I` (also `y ≠ I.left`), the value `μA μ (I.left, y)` is not
strictly greater than `μA μ (I.left, x)`.

Interpretation: `x` is a maximizer of the function `y ↦ μA μ (I.left, y)` among interior points.
API note: the predicate is written in a negated `>` form to match later rewriting patterns.
-/
def S₁I {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x) : Prop :=
∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) →
  ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ >
    μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩


/-
Auxiliary predicate `S₂I` (“minimality among ties”).

For the same situation as `S₁I`, the predicate `S₂I μ I x` says: whenever another `y` has the same
value `μA μ (I.left, y) = μA μ (I.left, x)`, then `y ≤ x`.

Interpretation: among all maximizers, `x` is chosen to be the greatest element with respect to `≤`.
This tie-breaking condition is important for uniqueness/canonical choice arguments.
-/
def S₂I {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x) : Prop :=
∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) →
  μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ =
  μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.1 hx⟩ → y ≤ x


/-
`StI μ I` is the set of “stable breakpoints” inside an interval `I`.

An element `l` belongs to `StI μ I` if it lies in `I`, is not the left endpoint, and satisfies both
selection properties `S₁I` and `S₂I`. This packages the notion of a canonical choice of breakpoint.
-/
def StI {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Set ℒ :=
{l : ℒ | ∃ hlI : InIntvl I l , ∃ hl : I.val.1 ≠ l ,  (S₁I μ I l hlI hl) ∧ (S₂I μ I l hlI hl)}


/-
The global set of stable breakpoints for the total interval.

This is simply `StI μ TotIntvl`, but provided as a convenient abbreviation for statements on `ℒ`.
-/
def St {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Set ℒ :=
StI μ TotIntvl


/-
Interval-local semistability: the right endpoint of `I` is a stable breakpoint for `I`.

In other words, `I` is semistable if `I.right ∈ StI μ I`.
-/
def semistableI {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := I.val.2 ∈ StI μ I


/-
Global semistability class.

This expresses that for every `x ≠ ⊥`, the value `μA μ (⊥,x)` is not strictly greater than the
global value `μA μ (⊥,⊤)`.

Interpretation: no proper initial segment yields a strictly better `μA`-value than the whole object.
API note: formulated as a class with a single field `semistable`.
-/
class Semistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  semistable : ∀x : ℒ, (hx : x ≠ ⊥) →
    ¬ μA μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ > μA μ ⟨(⊥,⊤),bot_lt_top⟩

/-
Global stability class.

This strengthens `Semistable μ` by requiring strict inequality: for any proper `x` (non-bottom and
not-top), the value `μA μ (⊥,x)` must be different from the global value `μA μ (⊥,⊤)`.

API note: we extend `Semistable μ` to reuse the semistability field and allow downstream lemmas to
accept `Stable μ` where `Semistable μ` is required.
-/
class Stable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) extends Semistable μ where
  stable : ∀x : ℒ, (hx : x ≠ ⊥) → x ≠ ⊤ →
    μA μ ⟨(⊥,x), bot_lt_iff_ne_bot.2 hx⟩ ≠ μA μ ⟨(⊥,⊤),bot_lt_top⟩

end HarderNarasimhan
