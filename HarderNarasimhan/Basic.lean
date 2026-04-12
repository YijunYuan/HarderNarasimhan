/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic

namespace HarderNarasimhan

/-!
This file provides the basic interval language and the core “extremal value” constructions derived
from
an interval-indexed function `μ : {p : ℒ × ℒ // p.1 < p.2} → S`.

The intended picture is that `ℒ` is a bounded poset (often a lattice in later files), `S` is a
complete lattice
(typically a linearly ordered type or an ordered commutative group in applications), and
`μ (a,b)` measures
some quantity associated to the strict interval `(a,b)`.

Core API:
- `InIntvl I x` is the predicate `a ≤ x ≤ b` for a strict interval `I = (a,b)`.
- `TotIntvl` is the total interval `(⊥, ⊤)`.
- `μmax μ I` is a supremum of `μ (a,u)` over interior points `u` of `I` (excluding the left endpoint
  ).
- `μmin μ I` is the dual infimum of `μ (u,b)` over interior points `u` (excluding the right endpoint
  ).
- `μA` and `μB` iterate these extremal operations in the two directions; `μAstar`/`μBstar`
  specialize to `TotIntvl`.
- `IsComparable` is a convenience predicate for comparability in a partial order.
- `IsAttained` records that the infimum defining `μA` is realized by some `a`.

Design notes:
All constructions are expressed using `sSup`/`sInf` over explicit set comprehensions so that they
work
uniformly for any `CompleteLattice S`.
-/

/--
Membership predicate for a strict interval `I` in a partial order.

If `I = (a,b)` with `a < b`, then `InIntvl I x` means `a ≤ x ≤ b`.
This is used throughout as the “point lies in interval” hypothesis without introducing a dedicated
subtype.
-/
def InIntvl {ℒ : Type*} [PartialOrder ℒ]
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) : Prop :=
  I.val.1 ≤ x ∧ x ≤ I.val.2


/--
The total interval `(⊥, ⊤)` in a nontrivial bounded poset.

API note: we package it as a strict pair so that it can be passed to constructions expecting an
interval.
-/
abbrev TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
{p : ℒ × ℒ // p.1 < p.2} := ⟨(⊥,⊤),bot_lt_top⟩


/--
Every element lies in the total interval.

This lemma is the canonical source of `InIntvl TotIntvl x`.
-/
@[simp] lemma in_TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (x : ℒ) :
InIntvl TotIntvl x := ⟨bot_le,le_top⟩


/--
`μmax μ I` is the supremum of `μ (I.left, u)` as `u` ranges over points in `I` distinct from the
left endpoint.

Intuition: this is a “best possible” value obtained by moving the right endpoint while keeping the
endpoint fixed.

API design:
- We quantify over `u : ℒ` together with a proof `h : InIntvl I u ∧ I.left ≠ u`.
- The strictness of `(I.left, u)` is derived from `I.left ≤ u` and `I.left ≠ u`.
- The result lives in any complete lattice `S` via `sSup`.
-/
def μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup {μ ⟨(I.val.1 , u), lt_of_le_of_ne h.1.1 h.2⟩ | (u : ℒ) (h : InIntvl I u ∧ I.val.1 ≠ u) }


/--
`μA μ I` is the infimum, over `a` in the interval distinct from the right endpoint, of `μmax`
computed on
the right-anchored subinterval `(a, I.right)`.

Intuition: this is an “optimal value” after allowing the left endpoint to vary, with `μmax`
capturing the
inner optimization.

API design:
- We use `sInf` in a complete lattice.
- Strictness of `(a, I.right)` is obtained from `a ≤ I.right` and `a ≠ I.right`.
-/
def μA {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sInf {μmax μ ⟨(a , I.val.2),(lt_of_le_of_ne ha.1.2 ha.2)⟩ |
  (a : ℒ) (ha : InIntvl I a ∧ a ≠ I.val.2)}


/--
`μAstar μ` is `μA μ` evaluated on the total interval `(⊥, ⊤)`.

This is a common global invariant used in later semistability and equilibrium statements.
-/
def μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : S :=
μA μ ⟨(⊥,⊤) , bot_lt_top⟩

@[simp] theorem μAstar_eq_μA_TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : μAstar μ = μA μ TotIntvl := rfl


/--
`μmin μ I` is the infimum of `μ (u, I.right)` as `u` ranges over points in `I` distinct from the
right endpoint.

This is the dual construction to `μmax`.
-/
def μmin {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sInf {μ ⟨(u, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩ | (u : ℒ) (h : InIntvl I u ∧ u ≠ I.val.2) }


/--
`μB μ I` is the supremum, over `a` in the interval distinct from the left endpoint, of `μmin`
computed on
the left-anchored subinterval `(I.left, a)`.

This is the dual counterpart of `μA` (sup over an outer parameter, inf as the inner optimization).
-/
def μB {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : S :=
sSup {μmin μ ⟨(I.val.1 , a),(lt_of_le_of_ne ha.1.1 ha.2)⟩ |
  (a : ℒ) (ha : InIntvl I a ∧ I.val.1 ≠ a)}


/--
`μBstar μ` is `μB μ` evaluated on the total interval `(⊥, ⊤)`.
-/
def μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : S :=
μB μ ⟨(⊥,⊤) , bot_lt_top⟩

@[simp] theorem μBstar_eq_μB_TotIntvl {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : μBstar μ = μB μ TotIntvl := rfl


/--
Convenience predicate: two elements are comparable in a partial order.

This is often used to state that a poset is (locally) a total preorder.
-/
def IsComparable {ℒ : Type*} [PartialOrder ℒ] : (x : ℒ) → (y : ℒ) → Prop :=
  fun x y => x ≤ y ∨ y ≤ x


/--
`IsAttained μ I` asserts that the infimum defining `μA μ I` is realized by some `a` in the interval.

More precisely, there exists `a` with `a` in `I` and `a ≠ I.right` such that
`μmax μ (a, I.right) = μA μ I`.

API note: this is phrased as an existential proposition rather than a structure, since we typically
only need existence to extract a witness in proofs.
-/
def IsAttained {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
  ∃ (a : ℒ) (haI : InIntvl I a) (ha : a ≠ I.val.2),
    μmax μ ⟨(a , I.val.2) , lt_of_le_of_ne haI.2 ha⟩ = μA μ I

end HarderNarasimhan
