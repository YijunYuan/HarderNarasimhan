/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Order.CompleteLattice.Defs
import HarderNarasimhan.StrictIntvl

/-!
# Payoff functions

This file defines `PayoffFunction ℒ S`, the bundled type of payoff functions of the
Harder–Narasimhan game: functions assigning to every strict interval of `ℒ` a payoff in `S`.
Payoff functions are applied via a `FunLike` coercion, so `μ ⟨a, b, h⟩` is the payoff of the
game played on the interval `(a, b)`.

For a complete lattice `S` we introduce the four extremal operations of the theory, each of
which is again a payoff function:

* `μ.max I`, the supremum of `μ (I.left, u)` over interior points `u`, and its order-dual
  companion `μ.min I`;
* `μ.A I`, the value of the game on `I` when player A moves first (an infimum of `μ.max`
  values over left endpoints), and its companion `μ.B I` for player B.

The global values of the game are `μ.A ⊤` and `μ.B ⊤` (denoted `μ_A^*` and `μ_B^*` in
[ChenJeannin]).

Finally, `μ.IsAttained I` records that the infimum defining `μ.A I` is attained.

## Implementation notes

All four operations are bounded suprema/infima in the dependent `⨆ (x) (hx : _), …` form, so
that the intervals appearing in the body can use the membership proof; basic `le_max`/`max_le`
style lemmas are provided so that downstream files never need to invoke the `iSup₂`/`iInf₂`
lemma families directly.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

/-- A *payoff function* on `ℒ` with values in `S`: a function assigning to every strict
interval of `ℒ` a payoff.  Payoff functions are applied via the `FunLike` coercion, so
`μ ⟨a, b, h⟩` is the payoff of the game played on the interval `(a, b)`. -/
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  /-- The underlying interval-indexed function.  Apply the payoff function via the coercion
  instead of using this projection directly. -/
  toFun : StrictIntvl ℒ → S

namespace PayoffFunction

variable {ℒ S : Type*}

section FunLike

variable [LT ℒ]

instance : FunLike (PayoffFunction ℒ S) (StrictIntvl ℒ) S where
  coe := toFun
  coe_injective μ ν h := by cases μ; cases ν; congr

@[simp] lemma coe_mk (f : StrictIntvl ℒ → S) : ⇑(mk f) = f := rfl

@[ext] lemma ext {μ ν : PayoffFunction ℒ S} (h : ∀ I, μ I = ν I) : μ = ν := DFunLike.ext μ ν h

end FunLike

variable [Preorder ℒ] [CompleteLattice S] (μ : PayoffFunction ℒ S)

/-! ### The extremal operations -/

/-- `μ.max I` is the supremum of `μ (I.left, u)` as `u` ranges over the points of `I` distinct
from the left endpoint.  This is a “best possible” payoff obtained by moving the right
endpoint while keeping the left endpoint fixed. -/
def max : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩⟩

lemma max_apply (I : StrictIntvl ℒ) :
    μ.max I = ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩ := rfl

/-- `μ.min I` is the infimum of `μ (u, I.right)` as `u` ranges over the points of `I` distinct
from the right endpoint.  This is the order-dual companion of `μ.max`. -/
def min : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨅ (u : ℒ) (hu : u ∈ Set.Ico I.left I.right), μ ⟨u, I.right, hu.2⟩⟩

lemma min_apply (I : StrictIntvl ℒ) :
    μ.min I = ⨅ (u : ℒ) (hu : u ∈ Set.Ico I.left I.right), μ ⟨u, I.right, hu.2⟩ := rfl

/-- `μ.A I` is the value of the game on `I` when player A moves first: the infimum, over left
endpoints `a` in the interval, of `μ.max` computed on the right-anchored subinterval
`(a, I.right)`.  The global value of the game for player A is `μ.A ⊤`. -/
def A : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩⟩

lemma A_apply (I : StrictIntvl ℒ) :
    μ.A I = ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩ := rfl

/-- `μ.B I` is the value of the game on `I` when player B moves first: the supremum, over
right endpoints `b` in the interval, of `μ.min` computed on the left-anchored subinterval
`(I.left, b)`.  This is the order-dual companion of `μ.A`; the global value of the game for
player B is `μ.B ⊤`. -/
def B : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ (b : ℒ) (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩⟩

lemma B_apply (I : StrictIntvl ℒ) :
    μ.B I = ⨆ (b : ℒ) (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩ := rfl

/-- `μ.IsAttained I` asserts that the infimum defining `μ.A I` is attained: there is a left
endpoint `a` in the interval with `μ.max (a, I.right) = μ.A I`. -/
def IsAttained (I : StrictIntvl ℒ) : Prop :=
  ∃ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩ = μ.A I

/-! ### Basic bounds

These lemmas interface the four operations with arbitrary bounds, so that downstream files
never need to unfold them to their `iSup₂`/`iInf₂` normal forms. -/

variable {μ} {I : StrictIntvl ℒ} {s : S}

lemma le_max {u : ℒ} (hu : u ∈ Set.Ioc I.left I.right) : μ ⟨I.left, u, hu.1⟩ ≤ μ.max I :=
  le_iSup₂_of_le u hu le_rfl

lemma max_le (h : ∀ u (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩ ≤ s) :
    μ.max I ≤ s :=
  iSup₂_le h

lemma min_le {u : ℒ} (hu : u ∈ Set.Ico I.left I.right) : μ.min I ≤ μ ⟨u, I.right, hu.2⟩ :=
  iInf₂_le_of_le u hu le_rfl

lemma le_min (h : ∀ u (hu : u ∈ Set.Ico I.left I.right), s ≤ μ ⟨u, I.right, hu.2⟩) :
    s ≤ μ.min I :=
  le_iInf₂ h

lemma A_le {a : ℒ} (ha : a ∈ Set.Ico I.left I.right) : μ.A I ≤ μ.max ⟨a, I.right, ha.2⟩ :=
  iInf₂_le_of_le a ha le_rfl

lemma le_A (h : ∀ a (ha : a ∈ Set.Ico I.left I.right), s ≤ μ.max ⟨a, I.right, ha.2⟩) :
    s ≤ μ.A I :=
  le_iInf₂ h

lemma le_B {b : ℒ} (hb : b ∈ Set.Ioc I.left I.right) : μ.min ⟨I.left, b, hb.1⟩ ≤ μ.B I :=
  le_iSup₂_of_le b hb le_rfl

lemma B_le (h : ∀ b (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩ ≤ s) :
    μ.B I ≤ s :=
  iSup₂_le h

/-- The payoff of an interval is bounded below by `μ.min`. -/
lemma min_le_apply : μ.min I ≤ μ I := min_le ⟨le_rfl, I.lt⟩

/-- The payoff of an interval is bounded above by `μ.max`. -/
lemma apply_le_max : μ I ≤ μ.max I := le_max ⟨I.lt, le_rfl⟩

/-- `μ.A` is antitone in the left endpoint: enlarging the interval to the left can only
decrease the first-player value.  This is a formal consequence of the definition of `μ.A` as
an infimum and needs no convexity. -/
lemma A_anti_left (μ : PayoffFunction ℒ S) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z) :
    μ.A ⟨x, z, h₁.trans h₂⟩ ≤ μ.A ⟨y, z, h₂⟩ :=
  le_A fun _ hv ↦ A_le (I := ⟨x, z, h₁.trans h₂⟩) ⟨(h₁.trans_le hv.1).le, hv.2⟩

end PayoffFunction

end HarderNarasimhan
