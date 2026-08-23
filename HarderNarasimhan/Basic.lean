/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic

/-!
This file provides the basic interval language and the core “extremal value” constructions derived
from an interval-indexed function `μ : Intvl ℒ → S`.

The intended picture is that `ℒ` is a bounded poset (often a lattice in later files), `S` is a
complete lattice (typically a linearly ordered type or an ordered commutative group in
applications), and `μ I` measures some quantity associated to the strict interval
`(I.left, I.right)`.

Core API:
- `Intvl ℒ` is the type of strict intervals: ordered pairs `left < right`.
- `x ∈ I` is the membership predicate `I.left ≤ x ≤ I.right`.
- `Intvl ℒ` is partially ordered by inclusion; when `ℒ` is a nontrivial bounded poset the total
  interval `(⊥, ⊤)` is its top element `⊤`.
- `μmax μ I` is a supremum of `μ ⟨I.left, u, _⟩` over interior points `u` of `I` (excluding the
  left endpoint).
- `μmin μ I` is the dual infimum of `μ ⟨u, I.right, _⟩` over interior points `u` (excluding the
  right endpoint).
- `μA` and `μB` iterate these extremal operations in the two directions; `μAstar`/`μBstar`
  specialize to the total interval `⊤`.
- `IsComparable` is a convenience predicate for comparability in a partial order.
- `IsAttained` records that the infimum defining `μA` is realized by some `a`.

Design notes:
All constructions are expressed using `sSup`/`sInf` over explicit set comprehensions so that they
work uniformly for any `CompleteLattice S`.
-/

namespace HarderNarasimhan

/--
A strict interval in `ℒ`: an ordered pair of endpoints `left < right`.

This is the index type of every interval-indexed invariant `μ` in the development.
Strictness is part of the data, so no use site ever needs to carry a nondegeneracy
side condition.
-/
@[ext]
structure Intvl (ℒ : Type*) [LT ℒ] where
  /-- The left endpoint. -/
  left : ℒ
  /-- The right endpoint. -/
  right : ℒ
  /-- The endpoints are in strict order. -/
  lt : left < right

namespace Intvl

/--
Membership in a strict interval: `x ∈ I` means `I.left ≤ x ∧ x ≤ I.right`.
-/
instance {ℒ : Type*} [LT ℒ] [LE ℒ] : Membership ℒ (Intvl ℒ) :=
  ⟨fun I x ↦ I.left ≤ x ∧ x ≤ I.right⟩

lemma mem_def {ℒ : Type*} [LT ℒ] [LE ℒ] {I : Intvl ℒ} {x : ℒ} :
    x ∈ I ↔ I.left ≤ x ∧ x ≤ I.right := Iff.rfl

/-- Membership agrees with membership in the closed interval `Set.Icc I.left I.right`. -/
lemma mem_iff_mem_Icc {ℒ : Type*} [Preorder ℒ] {I : Intvl ℒ} {x : ℒ} :
    x ∈ I ↔ x ∈ Set.Icc I.left I.right := Iff.rfl

@[simp] lemma left_mem {ℒ : Type*} [Preorder ℒ] (I : Intvl ℒ) : I.left ∈ I :=
  ⟨le_rfl, I.lt.le⟩

@[simp] lemma right_mem {ℒ : Type*} [Preorder ℒ] (I : Intvl ℒ) : I.right ∈ I :=
  ⟨I.lt.le, le_rfl⟩

/--
Strict intervals are partially ordered by inclusion: `I ≤ J` means `I` is a subinterval of `J`,
i.e. `J.left ≤ I.left ∧ I.right ≤ J.right`.
-/
instance {ℒ : Type*} [PartialOrder ℒ] : PartialOrder (Intvl ℒ) where
  le I J := J.left ≤ I.left ∧ I.right ≤ J.right
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hIJ hJK := ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩
  le_antisymm _ _ hIJ hJI := Intvl.ext (le_antisymm hJI.1 hIJ.1) (le_antisymm hIJ.2 hJI.2)

lemma le_def {ℒ : Type*} [PartialOrder ℒ] {I J : Intvl ℒ} :
    I ≤ J ↔ J.left ≤ I.left ∧ I.right ≤ J.right := Iff.rfl

/--
When `ℒ` is a nontrivial bounded poset, the total interval `(⊥, ⊤)` is the greatest strict
interval with respect to inclusion.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] : OrderTop (Intvl ℒ) where
  top := ⟨⊥, ⊤, bot_lt_top⟩
  le_top _ := ⟨bot_le, le_top⟩

@[simp] lemma left_top {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
    (⊤ : Intvl ℒ).left = ⊥ := rfl

@[simp] lemma right_top {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
    (⊤ : Intvl ℒ).right = ⊤ := rfl

/--
Every element lies in the total interval `⊤`.
-/
@[simp] lemma mem_top {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] (x : ℒ) :
    x ∈ (⊤ : Intvl ℒ) := ⟨bot_le, le_top⟩

/-- An interval with endpoints `⊥` and `⊤` is the total interval `⊤`, whatever the proof. -/
@[simp] lemma mk_bot_top {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
    (h : (⊥ : ℒ) < ⊤) : (⟨⊥, ⊤, h⟩ : Intvl ℒ) = ⊤ := rfl

end Intvl

/--
`μmax μ I` is the supremum of `μ ⟨I.left, u, _⟩` as `u` ranges over points in `I` distinct from the
left endpoint.

Intuition: this is a “best possible” value obtained by moving the right endpoint while keeping the
left endpoint fixed.

API design:
- We quantify over `u : ℒ` together with a proof `h : u ∈ I ∧ I.left ≠ u`.
- The strictness of `(I.left, u)` is derived from `I.left ≤ u` and `I.left ≠ u`.
- The result lives in any complete lattice `S` via `sSup`.
-/
def μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (I : Intvl ℒ) : S :=
sSup {μ ⟨I.left, u, lt_of_le_of_ne h.1.1 h.2⟩ | (u : ℒ) (h : u ∈ I ∧ I.left ≠ u)}

/--
`μA μ I` is the infimum, over `a` in the interval distinct from the right endpoint, of `μmax`
computed on the right-anchored subinterval `(a, I.right)`.

Intuition: this is an “optimal value” after allowing the left endpoint to vary, with `μmax`
capturing the inner optimization.

API design:
- We use `sInf` in a complete lattice.
- Strictness of `(a, I.right)` is obtained from `a ≤ I.right` and `a ≠ I.right`.
-/
def μA {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (I : Intvl ℒ) : S :=
sInf {μmax μ ⟨a, I.right, lt_of_le_of_ne ha.1.2 ha.2⟩ | (a : ℒ) (ha : a ∈ I ∧ a ≠ I.right)}

/--
`μAstar μ` is `μA μ` evaluated on the total interval `(⊥, ⊤)`.

This is a common global invariant used in later semistability and equilibrium statements.
-/
def μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) : S :=
μA μ ⊤

/--
`μmin μ I` is the infimum of `μ ⟨u, I.right, _⟩` as `u` ranges over points in `I` distinct from the
right endpoint.

This is the dual construction to `μmax`.
-/
def μmin {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (I : Intvl ℒ) : S :=
sInf {μ ⟨u, I.right, lt_of_le_of_ne h.1.2 h.2⟩ | (u : ℒ) (h : u ∈ I ∧ u ≠ I.right)}

/--
`μB μ I` is the supremum, over `a` in the interval distinct from the left endpoint, of `μmin`
computed on the left-anchored subinterval `(I.left, a)`.

This is the dual counterpart of `μA` (sup over an outer parameter, inf as the inner optimization).
-/
def μB {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (I : Intvl ℒ) : S :=
sSup {μmin μ ⟨I.left, a, lt_of_le_of_ne ha.1.1 ha.2⟩ | (a : ℒ) (ha : a ∈ I ∧ I.left ≠ a)}

/--
`μBstar μ` is `μB μ` evaluated on the total interval `(⊥, ⊤)`.
-/
def μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) : S :=
μB μ ⊤

/--
Convenience predicate: two elements are comparable in a partial order.

This is often used to state that a poset is (locally) a total preorder.
-/
def IsComparable {ℒ : Type*} [PartialOrder ℒ] : (x : ℒ) → (y : ℒ) → Prop :=
  fun x y => x ≤ y ∨ y ≤ x

/--
`IsAttained μ I` asserts that the infimum defining `μA μ I` is realized by some `a` in the interval.

More precisely, there exists `a` with `a ∈ I` and `a ≠ I.right` such that
`μmax μ ⟨a, I.right, _⟩ = μA μ I`.

API note: this is phrased as an existential proposition rather than a structure, since we typically
only need existence to extract a witness in proofs.
-/
def IsAttained {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (I : Intvl ℒ) : Prop :=
  ∃ (a : ℒ) (haI : a ∈ I) (ha : a ≠ I.right),
    μmax μ ⟨a, I.right, lt_of_le_of_ne haI.2 ha⟩ = μA μ I

end HarderNarasimhan
