/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.PayoffFunction.Defs

/-!
This file provides the core “extremal value” constructions derived from an interval-indexed
function `μ : PayoffFunction ℒ S`.

NOTE (refactor in progress): this transitional file will be replaced by
`HarderNarasimhan.PayoffFunction.Defs`, where these constructions become `PayoffFunction.max`,
`PayoffFunction.min`, `PayoffFunction.A` and `PayoffFunction.B`.

Core API:
- `μmax μ I` is a supremum of `μ ⟨I.left, u, _⟩` over interior points `u` of `I` (excluding the
  left endpoint).
- `μmin μ I` is the dual infimum of `μ ⟨u, I.right, _⟩` over interior points `u` (excluding the
  right endpoint).
- `μA` and `μB` iterate these extremal operations in the two directions; `μAstar`/`μBstar`
  specialize to the total interval `⊤`.
- `IsAttained` records that the infimum defining `μA` is realized by some `a`.
-/

namespace HarderNarasimhan

/--
`μmax μ I` is the supremum of `μ ⟨I.left, u, _⟩` as `u` ranges over points in `I` distinct from the
left endpoint.
-/
def μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : PayoffFunction ℒ S :=
⟨fun I ↦ ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩⟩

/--
`μA μ I` is the infimum, over `a` in the interval distinct from the right endpoint, of `μmax`
computed on the right-anchored subinterval `(a, I.right)`.
-/
def μA {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : PayoffFunction ℒ S :=
⟨fun I ↦ ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μmax μ ⟨a, I.right, ha.2⟩⟩

/--
`μAstar μ` is `μA μ` evaluated on the total interval `(⊥, ⊤)`.
-/
def μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : S :=
μA μ ⊤

/--
`μmin μ I` is the infimum of `μ ⟨u, I.right, _⟩` as `u` ranges over points in `I` distinct from the
right endpoint.  This is the dual construction to `μmax`.
-/
def μmin {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : PayoffFunction ℒ S :=
⟨fun I ↦ ⨅ (u : ℒ) (hu : u ∈ Set.Ico I.left I.right), μ ⟨u, I.right, hu.2⟩⟩

/--
`μB μ I` is the supremum, over `a` in the interval distinct from the left endpoint, of `μmin`
computed on the left-anchored subinterval `(I.left, a)`.  This is the dual counterpart of `μA`.
-/
def μB {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : PayoffFunction ℒ S :=
⟨fun I ↦ ⨆ (a : ℒ) (ha : a ∈ Set.Ioc I.left I.right), μmin μ ⟨I.left, a, ha.1⟩⟩

/--
`μBstar μ` is `μB μ` evaluated on the total interval `(⊥, ⊤)`.
-/
def μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : S :=
μB μ ⊤

/--
`IsAttained μ I` asserts that the infimum defining `μA μ I` is realized by some `a` in the
interval: there exists `a ∈ Set.Ico I.left I.right` such that `μmax μ ⟨a, I.right, _⟩ = μA μ I`.
-/
def IsAttained {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop :=
  ∃ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right),
    μmax μ ⟨a, I.right, ha.2⟩ = μA μ I

end HarderNarasimhan
