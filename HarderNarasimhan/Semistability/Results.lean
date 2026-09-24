/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Semistability.Impl

/-!
# Semistability — numbered statements

The statements of §3.1 of *Harder–Narasimhan Games*. The set `μ.breakpoints ⊤` is `St(μ)`;
`WellFoundedGT` expresses the ascending chain condition. Definitions are in
`Semistability.Defs`, and the proofs are in `Semistability.Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open PayoffFunction Impl.PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [Nontrivial ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable (μ : PayoffFunction ℒ S)

/--
Proposition 3.2: an infinite value on `(x,z)` bounds the value on `(a,x)` by that on `(a,z)`.
-/
lemma proposition_3_2 (hμ : μ.IsConvex) {a x z : ℒ} (hax : a < x) (hxz : x < z)
    (h : μ.A ⟨x, z, hxz⟩ = ⊤) : μ.A ⟨a, x, hax⟩ ≤ μ.A ⟨a, z, hax.trans hxz⟩ :=
  IsConvexOn.A_le_of_A_eq_top (hμ.isConvexOn ⊤) (StrictIntvl.mem_top _)
    (StrictIntvl.mem_top _) hxz h (StrictIntvl.mem_top _) hax

/-- Corollary 3.3: an adjacent infinite value on every descending chain implies the μA-DCC. -/
lemma corollary_3_3 (hμ : μ.IsConvex)
    (h : ∀ f : ℕ → ℒ, (hf : StrictAnti f) →
      ∃ n : ℕ, μ.A ⟨f (n + 1), f n, hf (lt_add_one n)⟩ = ⊤) : μ.ADCC :=
  adcc_of_exists_A_eq_top (hμ.isConvexOn ⊤) h

/-- Proposition 3.4: the ascending chain condition and μA-DCC ensure that `St(μ)` is nonempty. -/
lemma proposition_3_4 [WellFoundedGT ℒ] [μ.ADCC] (hμ : μ.IsConvex) :
    (μ.breakpoints ⊤).Nonempty :=
  breakpoints_nonempty (hμ.isConvexOn ⊤)

/-- Remark 3.5: `St(μ)` has at most one element for linearly ordered payoffs. -/
lemma remark_3_5 {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)
    {x y : ℒ} (hx : x ∈ μ.breakpoints ⊤) (hy : y ∈ μ.breakpoints ⊤) : x = y :=
  IsBreakpoint.eq hx hy

/-- Proposition 3.7: a breakpoint cuts out a semistable initial segment and bounds right values. -/
lemma proposition_3_7 (hμ : μ.IsConvex) {x : ℒ} (hx : μ.IsBreakpoint ⊤ x) :
    (μ.restrict ⟨⊥, x, hx.left_lt⟩).IsSemistable ∧
    ∀ y : ℒ, (hxy : x < y) → ¬ μ.A ⟨⊥, x, hx.left_lt⟩ ≤ μ.A ⟨x, y, hxy⟩ :=
  ⟨IsBreakpoint.isSemistable_restrict hx,
    fun y hxy ↦ IsBreakpoint.not_A_le hx (hμ.isConvexOn ⊤) (StrictIntvl.mem_top y) hxy⟩

/--
Proposition 3.8: totality and a greatest element of `St(μ)`, and the value beyond a breakpoint.
The greatest-element conclusion uses μA-DCC to ensure nonemptiness via Proposition 3.4.
-/
lemma proposition_3_8 [WellFoundedGT ℒ] (hμ : μ.IsConvex)
    (h : Std.Total (· ≤ · : S → S → Prop) ∨
      ∀ z : ℒ, (hz : ⊥ < z) → μ.IsAttained ⟨⊥, z, hz⟩) :
    (Std.Total (· ≤ · : μ.breakpoints ⊤ → μ.breakpoints ⊤ → Prop) ∧
      (μ.ADCC → ∃ s : ℒ, IsGreatest (μ.breakpoints ⊤) s)) ∧
    ∀ x : ℒ, (hx : μ.IsBreakpoint ⊤ x) → ∀ y : ℒ, (hxy : x < y) →
      μ.A ⟨⊥, y, hx.left_lt.trans hxy⟩ = μ.A ⟨x, y, hxy⟩ := by
  have h' := h.imp_right fun ha z (_ : z ∈ (⊤ : StrictIntvl ℒ)) hz ↦
    ha z (bot_le.lt_of_ne hz)
  exact ⟨⟨breakpoints_total (hμ.isConvexOn ⊤) h',
      fun hDCC ↦ @exists_isGreatest_breakpoints ℒ S _ _ μ ⊤ _ hDCC (hμ.isConvexOn ⊤) h'⟩,
    fun x hx y hxy ↦ IsBreakpoint.A_eq_A_of_lt hx (hμ.isConvexOn ⊤) h' (StrictIntvl.mem_top y) hxy⟩

end HarderNarasimhan
