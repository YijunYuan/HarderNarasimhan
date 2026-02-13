/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Semistability.Impl
import HarderNarasimhan.Semistability.Translation

/-!
This file collects the public-facing statements from the semistability chapter.

The heavy lifting is done in `HarderNarasimhan.Semistability.Impl`; here we:

* restate the main propositions/remarks using the global interval `TotIntvl` and the
  global predicates `St`/`Semistable`, and
* provide short aliases that match the numbering used in the accompanying notes.

All proofs are thin wrappers around the internal lemmas, mostly converting between
`Convex` and its interval-local variant `ConvexI`.

API overview:

* Import this file to use the numbered statements (`proposition_3_…`, `remark_3_…`, etc.) without
  depending on implementation details.
* When you need the underlying definitions/classes (e.g. `Semistable`, `Stable`, `St`, `StI`), use
  `HarderNarasimhan.Semistability.Defs`.
-/

namespace HarderNarasimhan

/-
Public wrapper for the internal convexity-driven monotonicity statement.

Intuitively: if the right endpoint `(x,z)` has maximal `μA` (equal to `⊤`), then
moving the left endpoint further left cannot decrease the `μA` value when comparing
the short interval `(a,x)` against the longer one `(a,z)`.

This is a typical “convexity along a chain” consequence, stated using the global
notation `Convex`.
-/
lemma proposition_3_2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (x : ℒ) (z : ℒ) (h : x < z)
  (h' : μA μ ⟨(x, z), h⟩ = ⊤)
  (a : ℒ) (hax : a < x) :
------------
  μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩
------------
  := by
    rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
    exact impl.prop3d2 TotIntvl μ hμcvx x (in_TotIntvl x) z
      (in_TotIntvl z) h h' a (in_TotIntvl a) hax


/-(
Re-export of the internal corollary `impl.cor3d3` under the name used in the paper.

This is kept as an `alias` to avoid duplicating proof terms.
-/
alias corollary_3_3 := impl.cor3d3


/-
Existence of a global “stable breakpoint”.

Under the descending chain condition for `μA` and convexity of `μ`, the set `St μ`
of stable elements is nonempty. The internal proof constructs such a breakpoint by a
well-founded recursion.

API note: this is a common starting point for constructing filtrations.
-/
lemma proposition_3_4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (hμDCC : μA_DescendingChainCondition μ) (hμcvx : Convex μ) :
------------
  (St μ).Nonempty
------------
  := by
    rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
    exact impl.prop3d4 μ hμDCC TotIntvl hμcvx


/-
Uniqueness of stable breakpoints in a linearly ordered codomain.

When `S` is a complete linear order, the internal remark shows that `St μ` has at
most one element, hence any two chosen stable points must be equal.
-/
lemma remark_3_5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type*} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (hxSt : x ∈ St μ)
  (y : ℒ) (hySt : y ∈ St μ) :
------------
  x = y
------------
  := impl.rmk3d5 μ TotIntvl x hxSt y hySt


/-
Semistability of the initial segment and the “no improvement to the right” property.
If `x ∈ St μ`, then:

1. the restriction of `μ` to the interval `(⊥, x)` is semistable, and
2. for any `y > x`, the `μA`-slope on `(⊥, x)` is *not* dominated by the slope on
   `(x, y)`.

This packages the two internal statements `impl.prop3d7₁` and `impl.prop3d7₂`.

API note: this lemma is a key interface for working with `St μ`.
-/
lemma proposition_3_7 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (x : ℒ) (hxSt : x ∈ St μ) :
------------
  /- `(1)` -/
  Semistable  (Resμ ⟨(⊥, x), lt_of_le_of_ne bot_le hxSt.out.choose_spec.choose⟩ μ)
  ∧
  /- `(2)` -/
  ∀ y : ℒ, (hy : y > x) →
    ¬ μA μ ⟨(⊥ , x) , lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤
      μA μ ⟨(x, y), hy⟩
------------
  := by
    rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
    constructor
    · apply (semistableI_iff μ ⟨(⊥, x), lt_of_le_of_ne bot_le hxSt.out.choose_spec.choose⟩).1 <|
        impl.prop3d7₁ μ TotIntvl x hxSt
    · exact fun y hy ↦ impl.prop3d7₂ μ TotIntvl hμcvx x hxSt y (in_TotIntvl y) hy


/-
Totality/maximality consequences and the slope decomposition formula.
Assuming convexity and an additional admissibility hypothesis (either totality of
`≤` on `S`, or an attainment condition on `μ`), the internal results show:

1. `St μ` is totally ordered and, under DCC, admits a greatest element; and
2. for any stable breakpoint `x` and any `y > x`, the slope from `⊥` to `y` equals
   the slope from `x` to `y`.

This is a thin wrapper around `impl.prop3d8₁`, `impl.prop3d8₁'`, and `impl.prop3d8₂`.

API note: use this lemma to compare `μA` across different left endpoints once a stable
breakpoint is chosen.
-/
lemma proposition_3_8 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hz : ⊥ ≠ z) → IsAttained μ ⟨(⊥ , z) , lt_of_le_of_ne bot_le hz⟩) :
------------
  (
  /- `(1)` -/
  @Std.Total (St μ) (· ≤ ·) ∧ (μA_DescendingChainCondition μ → ∃ s : ℒ, IsGreatest (St μ) s)
  ) ∧
  /- `(2)` -/
  ∀ x : ℒ, (hxSt : x ∈ St μ) →
  (∀ y : ℒ, (hxy : y > x) →
    μA μ ⟨(⊥ , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩)
------------
 := by
  rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
  constructor
  · constructor
    · rcases h with c1 | c2
      · exact impl.prop3d8₁ μ TotIntvl hμcvx (Or.inl c1)
      · exact impl.prop3d8₁ μ TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz)
    · intro hμDCC
      rcases h with c1 | c2
      · exact impl.prop3d8₁' μ hμDCC TotIntvl hμcvx (Or.inl c1)
      · exact impl.prop3d8₁' μ hμDCC TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz)
  · intro x hxSt y hxy
    rcases h with c1 | c2
    · exact impl.prop3d8₂ μ TotIntvl hμcvx (Or.inl c1) x hxSt y (in_TotIntvl y) hxy
    · exact impl.prop3d8₂ μ TotIntvl hμcvx (Or.inr fun z _ hz ↦ c2 z hz)
        x hxSt y (in_TotIntvl y) hxy

end HarderNarasimhan
