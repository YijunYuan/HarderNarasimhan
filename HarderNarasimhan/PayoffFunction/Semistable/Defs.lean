/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict

/-!
# Semistability and breakpoints

A payoff function is semistable if no initial segment `(⊥, x)` has a strictly larger
`μ.A`-value than the total interval. It is stable if, in addition, equality only occurs at
`x = ⊤`.

A breakpoint of `μ` on `I` is a point `x ∈ I` above `I.left` such that the value
`μ.A (I.left, x)` is maximal among the initial-segment values and `x` is greatest among the
points with that value. When the payoffs are linearly ordered, this value is a maximum.
Breakpoints give the successive cuts in Harder–Narasimhan filtrations.

## Main definitions

* `HarderNarasimhan.PayoffFunction.IsSemistable`, `HarderNarasimhan.PayoffFunction.IsStable`:
  semistability and stability.
* `HarderNarasimhan.PayoffFunction.IsBreakpoint`: the breakpoint predicate.
* `HarderNarasimhan.PayoffFunction.ADCC`: a descending chain condition excluding an infinite
  strict increase of `μ.A` along a decreasing sequence of right endpoints.

The right endpoint is a breakpoint precisely when the restriction to the interval is
semistable; see `HarderNarasimhan.PayoffFunction.isBreakpoint_right_iff`. Existence of
breakpoints is proved in `HarderNarasimhan/PayoffFunction/Semistable/Breakpoints.lean`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Preorder

variable [Preorder ℒ] [CompleteLattice S]

/-- The descending chain condition for `μ.A`: for every `a` and every strictly decreasing
sequence `f` above `a`, some adjacent pair fails to give a strict increase of `μ.A (a, f n)`. -/
class ADCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Some adjacent pair fails to give a strict increase of the `μ.A`-values. -/
  dcc : ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → StrictAnti f →
    ∃ N : ℕ, ¬ μ.A ⟨a, f N, h₁ N⟩ < μ.A ⟨a, f <| N + 1, h₁ <| N + 1⟩

end Preorder

section PartialOrder

variable [PartialOrder ℒ] [CompleteLattice S]

variable (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ)

/-- A breakpoint of `μ` on `I` is a point `x ∈ I` with `I.left < x` such that no value
`μ.A (I.left, y)` with `I.left < y ≤ I.right` is strictly larger than `μ.A (I.left, x)`, and
every such point with the same value lies below `x`.

The value at a breakpoint is maximal, and is a maximum when `S` is linearly ordered.
For slope payoffs, breakpoints play the role of maximal destabilising subobjects. The right
endpoint is also allowed, as occurs for semistable intervals. -/
structure IsBreakpoint (x : ℒ) : Prop where
  /-- A breakpoint lies in the interval. -/
  mem : x ∈ I
  /-- A breakpoint is distinct from the left endpoint. -/
  ne_left : I.left ≠ x
  /-- No initial segment has a strictly larger `μ.A`-value. -/
  not_lt : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    ¬ μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ < μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩
  /-- Every point with the same `μ.A`-value lies below `x`. -/
  le_of_eq : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) →
    μ.A ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ = μ.A ⟨I.left, x, lt_of_le_of_ne mem.1 ne_left⟩ →
      y ≤ x

/-- The set of breakpoints of `μ` on `I`. -/
def breakpoints : Set ℒ := {x | μ.IsBreakpoint I x}

variable {μ I}

@[simp] lemma mem_breakpoints {x : ℒ} : x ∈ μ.breakpoints I ↔ μ.IsBreakpoint I x := Iff.rfl

/-- A breakpoint lies strictly above the left endpoint. -/
lemma IsBreakpoint.left_lt {x : ℒ} (hx : μ.IsBreakpoint I x) : I.left < x :=
  lt_of_le_of_ne hx.mem.1 hx.ne_left

end PartialOrder

section BoundedOrder

variable [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A payoff function is semistable if no initial segment `(⊥, x)` has a strictly larger
`μ.A`-value than the total interval. -/
class IsSemistable (μ : PayoffFunction ℒ S) : Prop where
  /-- No initial segment has a strictly larger `μ.A`-value than the total interval. -/
  not_lt : ∀ x : ℒ, (hx : ⊥ < x) → ¬ μ.A ⊤ < μ.A ⟨⊥, x, hx⟩

/-- A payoff function is stable if it is semistable and no proper initial segment has the
same `μ.A`-value as the total interval. -/
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

/-- The right endpoint is a breakpoint iff the restriction to the interval is semistable. -/
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
    simpa only [A_restrict_apply, StrictIntvl.ofSub_top]

end Restrict

end PayoffFunction

end HarderNarasimhan
