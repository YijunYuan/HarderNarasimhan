/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict

/-!
# Semistable payoff functions and breakpoints

This file defines the (semi)stability notions of the Harder–Narasimhan game and the
*breakpoint* predicate underlying the construction of Harder–Narasimhan filtrations.

A payoff function is *semistable* if no proper initial segment `(⊥, x)` beats the total
interval in first-player value, and *stable* if in addition no proper initial segment ties
with it.  A *breakpoint* of `μ` on an interval `I` is a point `x` which maximises the
first-player value `μ.A (I.left, ·)` among interior initial segments of `I` and is the
greatest point doing so; breakpoints are the canonical cut points from which
Harder–Narasimhan filtrations are built (see `PayoffFunction.Semistable.Breakpoints`).

The descending chain condition `PayoffFunction.ADCC` rules out infinite strict improvement
of `μ.A` along descending chains and is the standing hypothesis for the existence of
breakpoints.

## Main definitions

* `PayoffFunction.IsSemistable`, `PayoffFunction.IsStable` : the (semi)stability typeclasses.
* `PayoffFunction.IsBreakpoint`, `PayoffFunction.breakpoints` : the breakpoint predicate on
  an interval, and the set of breakpoints.
* `PayoffFunction.ADCC` : the descending chain condition for `μ.A`.

## Main results

* `isSemistable_iff_isBreakpoint_top` : global semistability says exactly that `⊤` is a
  breakpoint of the total interval.
* `isBreakpoint_right_iff` : `I.right` is a breakpoint of `I` iff the restriction
  `μ.restrict I` is semistable.  This is the key translation between the ambient-interval
  and the restricted viewpoints.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Preorder

variable [Preorder ℒ] [CompleteLattice S]

/-- The *descending chain condition* for `μ.A` (`ADCC`): for every base point `a` and every
strictly descending chain `f` above `a`, the values `μ.A (a, f N)` cannot strictly increase
forever.  This is the standing termination hypothesis for the breakpoint construction. -/
class ADCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Along a strictly descending chain the `μ.A`-values eventually stop improving. -/
  dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μ.A ⟨a, f N, h₁ N⟩ < μ.A ⟨a, f <| N + 1, h₁ <| N + 1⟩

end Preorder

section PartialOrder

variable [PartialOrder ℒ] [CompleteLattice S]

variable (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)

/-- `x` is a *breakpoint* of `μ` on `I`: among interior initial segments `(I.left, y)` of
`I`, the segment cut at `x` maximises the first-player value `μ.A`, and `x` is the greatest
point doing so.  Breakpoints are the canonical cut points of the Harder–Narasimhan theory.

Breakpoints play the role of the *maximal destabilising subobjects* of the classical
Harder–Narasimhan theory of vector bundles: the first step of the classical filtration is
the subobject that maximises the slope and is greatest among the maximisers, exactly as a
breakpoint maximises `μ.A (I.left, ·)` and is the greatest maximiser, and such elements are
accordingly called *maximal destabilising elements* in the literature.  The neutral name
*breakpoint* is preferred here because for a semistable payoff function the top element `⊤`
is itself a breakpoint of the total interval (`isSemistable_iff_isBreakpoint_top`), and
calling it "destabilising" would then be a misnomer. -/
structure IsBreakpoint (x : ℒ) : Prop where
  /-- A breakpoint lies in the interval. -/
  mem : x ∈ I
  /-- A breakpoint is distinct from the left endpoint. -/
  ne_left : I.left ≠ x
  /-- No interior initial segment has a strictly larger first-player value. -/
  not_lt : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    ¬ μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ < μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩
  /-- Among the maximisers, `x` is the greatest. -/
  le_of_eq : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ = μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ →
      y ≤ x

/-- The set of breakpoints of `μ` on `I`.  See `PayoffFunction.IsBreakpoint` for the
relation with the maximal destabilising subobjects of the classical theory. -/
def breakpoints : Set ℒ := {x | μ.IsBreakpoint I x}

variable {μ I}

@[simp] lemma mem_breakpoints {x : ℒ} : x ∈ μ.breakpoints I ↔ μ.IsBreakpoint I x := Iff.rfl

/-- A breakpoint lies strictly above the left endpoint. -/
lemma IsBreakpoint.left_lt {x : ℒ} (hx : μ.IsBreakpoint I x) : I.left < x :=
  lt_of_le_of_ne hx.mem.1 hx.ne_left

end PartialOrder

section BoundedOrder

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A payoff function is *semistable* if no proper initial segment `(⊥, x)` has a strictly
larger first-player value than the total interval: the whole object is already an optimal
first move. -/
class IsSemistable (μ : PayoffFunction ℒ S) : Prop where
  /-- No proper initial segment beats the total interval. -/
  not_lt : ∀ x : ℒ, (hx : ⊥ < x) → ¬ μ.A ⊤ < μ.A ⟨⊥, x, hx⟩

/-- A payoff function is *stable* if it is semistable and no proper initial segment `(⊥, x)`
with `x < ⊤` ties with the total interval in first-player value. -/
class IsStable (μ : PayoffFunction ℒ S) : Prop extends μ.IsSemistable where
  /-- No proper initial segment ties with the total interval. -/
  ne : ∀ x : ℒ, (hx : ⊥ < x) → x < ⊤ → μ.A ⟨⊥, x, hx⟩ ≠ μ.A ⊤

variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Global semistability says exactly that `⊤` is a breakpoint of the total interval. -/
theorem isSemistable_iff_isBreakpoint_top :
    μ.IsSemistable ↔ μ.IsBreakpoint ⊤ (⊤ : ℒ) := by
  constructor
  · exact fun h ↦
      { mem := StrictIntvl.mem_top _
        ne_left := bot_lt_top.ne
        not_lt := fun y _ hy ↦ h.not_lt y (bot_le.lt_of_ne hy)
        le_of_eq := fun y _ _ _ ↦ le_top }
  · exact fun h ↦ ⟨fun x hx ↦ h.not_lt x (StrictIntvl.mem_top x) hx.ne⟩

end BoundedOrder

section Restrict

variable [PartialOrder ℒ] [CompleteLattice S] {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- `I.right` is a breakpoint of `I` iff the restriction `μ.restrict I` is semistable.
This is the key translation between the ambient-interval viewpoint and the viewpoint of the
interval as a self-contained bounded order. -/
theorem isBreakpoint_right_iff :
    μ.IsBreakpoint I I.right ↔ (μ.restrict I).IsSemistable := by
  constructor
  · intro h
    refine ⟨fun y hy hcon ↦ ?_⟩
    simp only [A_restrict_apply] at hcon
    exact h.not_lt y.val y.prop (fun hc ↦ hy.ne (Subtype.ext hc)) hcon
  · intro h
    refine ⟨I.right_mem, I.lt.ne, fun y hyI hy hcon ↦ ?_, fun y hyI _ _ ↦ hyI.2⟩
    have hy' : (⊥ : ↥I) < ⟨y, hyI⟩ :=
      lt_of_le_of_ne bot_le fun hc ↦ hy (congrArg Subtype.val hc)
    refine h.not_lt ⟨y, hyI⟩ hy' ?_
    simp only [A_restrict_apply, StrictIntvl.ofSub_top]
    exact hcon

end Restrict

end PayoffFunction

end HarderNarasimhan
