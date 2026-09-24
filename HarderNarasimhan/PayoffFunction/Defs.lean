/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.StrictIntvl
public import Mathlib.Order.CompleteLattice.Defs

/-!
# Payoff functions

A payoff function assigns a value to each strict interval of an ordered type. In the
Harder–Narasimhan games, player A chooses a left endpoint and seeks to minimise the payoff,
while player B chooses a right endpoint and seeks to maximise it. The endpoints must satisfy
`a < b`.

For a complete lattice of payoffs, `μ.max I` is the supremum over right endpoints with the
left endpoint fixed, and `μ.min I` is the infimum over left endpoints with the right endpoint
fixed. The game values `μ.A I` and `μ.B I` correspond to A and B moving first, respectively.
When the underlying order is bounded and nontrivial, the global game values are `μ.A ⊤`
and `μ.B ⊤`.

## Main definitions

* `HarderNarasimhan.PayoffFunction`: payoff functions on strict intervals.
* `HarderNarasimhan.PayoffFunction.A`, `HarderNarasimhan.PayoffFunction.B`: the two game values.
* `HarderNarasimhan.PayoffFunction.IsAttained`: attainment of the infimum defining `μ.A I`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

/-- Section 2.1, the payoff function used in Definition 2.1. A payoff function assigns a value in
`S` to each strict interval of `ℒ`.

The coercion to functions allows the notation `μ ⟨a, b, h⟩` for the payoff on an interval
with endpoints `a < b`. -/
structure PayoffFunction (ℒ : Type*) [LT ℒ] (S : Type*) where
  /-- Definition 2.1: the underlying function on strict intervals. -/
  toFun : StrictIntvl ℒ → S

namespace PayoffFunction

variable {ℒ S : Type*}

section FunLike

variable [LT ℒ]

/-- Auxiliary payoff API for Definition 2.1: the induced instance. -/
instance : FunLike (PayoffFunction ℒ S) (StrictIntvl ℒ) S where
  coe := toFun
  coe_injective μ ν h := by cases μ; cases ν; congr

/-- Auxiliary payoff API for Definition 2.1: coe mk. -/
@[simp] lemma coe_mk (f : StrictIntvl ℒ → S) : ⇑(mk f) = f := rfl

/-- Auxiliary payoff API for Definition 2.1: ext. -/
@[ext] lemma ext {μ ν : PayoffFunction ℒ S} (h : ∀ I, μ I = ν I) : μ = ν := DFunLike.ext μ ν h

/-- Section 4.2, the dual game used in Proposition 4.3. The payoff function on the order duals of
`ℒ` and `S`, obtained by reversing the
endpoints. Order duality exchanges the two players; see
`HarderNarasimhan.Impl.PayoffFunction.A_top_dual` and
`HarderNarasimhan.Impl.PayoffFunction.B_top_dual`. -/
def dual (μ : PayoffFunction ℒ S) : PayoffFunction ℒᵒᵈ Sᵒᵈ :=
  ⟨fun p ↦ OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩⟩

/-- Auxiliary identity for the duality in Proposition 4.3: dual apply. -/
@[simp] lemma dual_apply (μ : PayoffFunction ℒ S) (p : StrictIntvl ℒᵒᵈ) :
    μ.dual p = OrderDual.toDual (μ ⟨p.right, p.left, p.lt⟩) :=
  rfl

end FunLike

variable [Preorder ℒ] [CompleteLattice S] (μ : PayoffFunction ℒ S)

/-! ### The extremal operations -/

/-- Notation 4.9 (also introduced after Definition 2.2). The supremum of the payoffs on `(I.left,
u)` for `I.left < u ≤ I.right`. -/
def max : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩⟩

/-- Notation 4.9, the supremum formula: max apply. -/
lemma max_apply (I : StrictIntvl ℒ) :
    μ.max I = ⨆ (u : ℒ) (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩ := rfl

/-- Notation 4.9. The infimum of the payoffs on `(u, I.right)` for `I.left ≤ u < I.right`. -/
def min : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨅ (u : ℒ) (hu : u ∈ Set.Ico I.left I.right), μ ⟨u, I.right, hu.2⟩⟩

/-- Notation 4.9, the infimum formula: min apply. -/
lemma min_apply (I : StrictIntvl ℒ) :
    μ.min I = ⨅ (u : ℒ) (hu : u ∈ Set.Ico I.left I.right), μ ⟨u, I.right, hu.2⟩ := rfl

/-- Definition 2.1 and Definition 2.2, equation (2.1). The value when player A moves first: the
infimum of `μ.max (a, I.right)` over
`I.left ≤ a < I.right`. -/
def A : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩⟩

/-- Definition 2.2, equation (2.1): A apply. -/
lemma A_apply (I : StrictIntvl ℒ) :
    μ.A I = ⨅ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩ := rfl

/-- Section 4.1 and Remark 4.10, the value when Bob moves first. The value when player B moves
first: the supremum of `μ.min (I.left, b)` over
`I.left < b ≤ I.right`. -/
def B : PayoffFunction ℒ S :=
  ⟨fun I ↦ ⨆ (b : ℒ) (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩⟩

/-- Remark 4.10, restricted to an interval: B apply. -/
lemma B_apply (I : StrictIntvl ℒ) :
    μ.B I = ⨆ (b : ℒ) (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩ := rfl

/-- Proposition 2.6(c), the attainment hypothesis. The infimum defining `μ.A I` is attained at
some left endpoint
`I.left ≤ a < I.right`. -/
def IsAttained (I : StrictIntvl ℒ) : Prop :=
  ∃ (a : ℒ) (ha : a ∈ Set.Ico I.left I.right), μ.max ⟨a, I.right, ha.2⟩ = μ.A I

/-! ### Basic bounds -/

variable {μ} {I : StrictIntvl ℒ} {s : S}

/-- Auxiliary supremum bound for Notation 4.9: le max. -/
lemma le_max {u : ℒ} (hu : u ∈ Set.Ioc I.left I.right) : μ ⟨I.left, u, hu.1⟩ ≤ μ.max I :=
  le_iSup₂_of_le u hu le_rfl

/-- Auxiliary supremum bound for Notation 4.9: max le. -/
lemma max_le (h : ∀ u (hu : u ∈ Set.Ioc I.left I.right), μ ⟨I.left, u, hu.1⟩ ≤ s) :
    μ.max I ≤ s :=
  iSup₂_le h

/-- Auxiliary infimum bound for Notation 4.9: min le. -/
lemma min_le {u : ℒ} (hu : u ∈ Set.Ico I.left I.right) : μ.min I ≤ μ ⟨u, I.right, hu.2⟩ :=
  iInf₂_le_of_le u hu le_rfl

/-- Auxiliary infimum bound for Notation 4.9: le min. -/
lemma le_min (h : ∀ u (hu : u ∈ Set.Ico I.left I.right), s ≤ μ ⟨u, I.right, hu.2⟩) :
    s ≤ μ.min I :=
  le_iInf₂ h

/-- Auxiliary infimum bound for Definition 2.2: A le. -/
lemma A_le {a : ℒ} (ha : a ∈ Set.Ico I.left I.right) : μ.A I ≤ μ.max ⟨a, I.right, ha.2⟩ :=
  iInf₂_le_of_le a ha le_rfl

/-- Auxiliary infimum bound for Definition 2.2: le A. -/
lemma le_A (h : ∀ a (ha : a ∈ Set.Ico I.left I.right), s ≤ μ.max ⟨a, I.right, ha.2⟩) :
    s ≤ μ.A I :=
  le_iInf₂ h

/-- Auxiliary supremum bound for Remark 4.10: le B. -/
lemma le_B {b : ℒ} (hb : b ∈ Set.Ioc I.left I.right) : μ.min ⟨I.left, b, hb.1⟩ ≤ μ.B I :=
  le_iSup₂_of_le b hb le_rfl

/-- Auxiliary supremum bound for Remark 4.10: B le. -/
lemma B_le (h : ∀ b (hb : b ∈ Set.Ioc I.left I.right), μ.min ⟨I.left, b, hb.1⟩ ≤ s) :
    μ.B I ≤ s :=
  iSup₂_le h

/-- Notation 4.9, the lower bound. The payoff of an interval is bounded below by `μ.min`. -/
lemma min_le_apply : μ.min I ≤ μ I := min_le ⟨le_rfl, I.lt⟩

/-- Notation 4.9, the upper bound. The payoff of an interval is bounded above by `μ.max`. -/
lemma apply_le_max : μ I ≤ μ.max I := le_max ⟨I.lt, le_rfl⟩

/-- Proposition 2.6, inequality (2.4). Extending an interval to the left cannot increase the value
when player A moves first. -/
lemma A_anti_left (μ : PayoffFunction ℒ S) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z) :
    μ.A ⟨x, z, h₁.trans h₂⟩ ≤ μ.A ⟨y, z, h₂⟩ :=
  le_A fun _ hv ↦ A_le (I := ⟨x, z, h₁.trans h₂⟩) ⟨(h₁.trans_le hv.1).le, hv.2⟩


end PayoffFunction

end HarderNarasimhan
