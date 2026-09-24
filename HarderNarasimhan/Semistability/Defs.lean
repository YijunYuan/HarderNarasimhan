/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict

/-!
# Semistability — definitions

Definitions 3.1 and 3.6 of *Harder–Narasimhan Games*: the μA-descending chain condition,
breakpoints, semistability, and stability. The ascending chain condition in Definition 3.1
is represented by Mathlib's `WellFoundedGT`. Proofs are in `Semistability.Impl`, and the
numbered statements of §3.1 are in `Semistability.Results`.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Preorder

variable [Preorder ℒ] [CompleteLattice S]

/--
Definition 3.1 (the μA-descending chain condition). The descending chain condition for `μ.A`:
for every `a` and every strictly decreasing sequence `f` above `a`, some adjacent pair fails to
give a strict increase of `μ.A (a, f n)`.
-/
class ADCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Definition 3.1: some adjacent pair fails to give a strict increase of the `μ.A`-values. -/
  dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μ.A ⟨a, f N, h₁ N⟩ < μ.A ⟨a, f <| N + 1, h₁ <| N + 1⟩

end Preorder

section PartialOrder

variable [PartialOrder ℒ] [CompleteLattice S]

variable (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)

/--
Definition 3.6 and conditions (S1), (S2) of Proposition 3.4, on an interval. A breakpoint of `μ`
on `I` is a point `x ∈ I` with `I.left < x` such that no value `μ.A (I.left, y)` with `I.left <
y ≤ I.right` is strictly larger than `μ.A (I.left, x)`, and every such point with the same value
lies below `x`.

The value at a breakpoint is maximal, and is a maximum when `S` is linearly ordered. For slope
payoffs, breakpoints play the role of maximal destabilising subobjects. The right endpoint is
also allowed, as occurs for semistable intervals.
-/
structure IsBreakpoint (x : ℒ) : Prop where
  /-- Definition 3.6: a breakpoint lies in the interval. -/
  mem : x ∈ I
  /-- Definition 3.6: a breakpoint is distinct from the left endpoint. -/
  ne_left : I.left ≠ x
  /-- Definition 3.6: no initial segment has a strictly larger `μ.A`-value. -/
  not_lt : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    ¬ μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ < μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩
  /-- Definition 3.6: every point with the same `μ.A`-value lies below `x`. -/
  le_of_eq : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ = μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ →
      y ≤ x

/-- Definition 3.6 (the set St(μ)), on an interval. The set of breakpoints of `μ` on `I`. -/
def breakpoints : Set ℒ := {x | μ.IsBreakpoint I x}

variable {μ I}

/-- Auxiliary membership characterization for Definition 3.6. -/
@[simp] lemma mem_breakpoints {x : ℒ} : x ∈ μ.breakpoints I ↔ μ.IsBreakpoint I x := Iff.rfl

/--
Auxiliary endpoint property for Definition 3.6. A breakpoint lies strictly above the left
endpoint.
-/
lemma IsBreakpoint.left_lt {x : ℒ} (hx : μ.IsBreakpoint I x) : I.left < x :=
  lt_of_le_of_ne hx.mem.1 hx.ne_left

end PartialOrder

section BoundedOrder

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/--
Definition 3.6 (semistability). A payoff function is semistable if no initial segment `(⊥, x)`
has a strictly larger `μ.A`-value than the total interval.
-/
class IsSemistable (μ : PayoffFunction ℒ S) : Prop where
  /--
  Definition 3.6: no initial segment has a strictly larger `μ.A`-value than the total interval.
  -/
  not_lt : ∀ x : ℒ, (hx : ⊥ < x) → ¬ μ.A ⊤ < μ.A ⟨⊥, x, hx⟩

/--
Definition 3.6 (stability). A payoff function is stable if it is semistable and no proper
initial segment has the same `μ.A`-value as the total interval.
-/
class IsStable (μ : PayoffFunction ℒ S) : Prop extends μ.IsSemistable where
  /-- Definition 3.6: no proper initial segment ties with the total interval. -/
  ne : ∀ x : ℒ, (hx : ⊥ < x) → x < ⊤ → μ.A ⟨⊥, x, hx⟩ ≠ μ.A ⊤

end BoundedOrder

end PayoffFunction

end HarderNarasimhan
