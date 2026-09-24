/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.NashEquilibrium.Impl

/-!
# Section 4.4: Nash equilibrium and semistability — statements

The numbered comparison results; proofs and the descriptive API are in `NashEquilibrium.Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Remark 4.10. Comparing the two game values amounts to comparing every initial minimum with
every final maximum. -/
theorem remark_4_10 (μ : PayoffFunction ℒ S) :
    μ.B ⊤ ≤ μ.A ⊤ ↔ ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) →
      μ.min ⟨⊥, y, hy⟩ ≤ μ.max ⟨x, ⊤, lt_top_iff_ne_top.2 hx⟩ :=
  Impl.PayoffFunction.B_top_le_A_top_iff

/-- Proposition 4.11. Equality of the extremal payoffs implies the reverse game-value inequality;
the converse holds under both sets of first-mover hypotheses. -/
theorem proposition_4_11 (μ : PayoffFunction ℒ S) :
    (μ.min ⊤ = μ.max ⊤ → μ.B ⊤ ≤ μ.A ⊤) ∧
    (μ.WeakACC → μ.WeakSlopeLikeAtTop → μ.StrongDCC → μ.WeakSlopeLikeAtBot →
      μ.B ⊤ ≤ μ.A ⊤ → μ.min ⊤ = μ.max ⊤) :=
  ⟨Impl.PayoffFunction.B_top_le_A_top_of_min_eq_max,
    fun _ _ _ _ ↦ Impl.PayoffFunction.min_top_eq_max_top_of_B_top_le_A_top⟩

/-- Proposition 4.12. The local comparison turns the maximum equality into equality of minimum and
maximum. -/
theorem proposition_4_12 (μ : PayoffFunction ℒ S)
    (h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
      ¬ μ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
        μ ⊤ ≤ μ ⟨x, ⊤, lt_top_iff_ne_top.2 hx.2⟩) :
    μ.max ⊤ = μ ⊤ → μ.min ⊤ = μ.max ⊤ :=
  Impl.PayoffFunction.min_eq_max_of_max_eq h

/-- Proposition 4.14. The dual local comparison turns the minimum equality into equality of
maximum and minimum. -/
theorem proposition_4_14 (μ : PayoffFunction ℒ S)
    (h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
      μ ⟨⊥, x, bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ ⊤ ∨
        ¬ μ ⊤ ≤ μ ⟨x, ⊤, lt_top_iff_ne_top.2 hx.2⟩) :
    μ.min ⊤ = μ ⊤ → μ.max ⊤ = μ.min ⊤ :=
  Impl.PayoffFunction.max_eq_min_of_min_eq h

/-- Proposition 4.16 (1). For a slope-like payoff, the three extremal equalities are equivalent. -/
theorem proposition_4_16_1 (μ : PayoffFunction ℒ S) [μ.IsSlopeLike] :
    List.TFAE [μ.max ⊤ = μ ⊤, μ.min ⊤ = μ ⊤, μ.min ⊤ = μ.max ⊤] :=
  Impl.PayoffFunction.extremalPayoff_tfae

/-- Proposition 4.16 (2). With both chain conditions, the three equalities are also equivalent to
Nash equilibrium. -/
theorem proposition_4_16_2 (μ : PayoffFunction ℒ S) [μ.IsSlopeLike]
    [μ.WeakACC] [μ.StrongDCC] :
    List.TFAE [μ.max ⊤ = μ ⊤, μ.min ⊤ = μ ⊤, μ.min ⊤ = μ.max ⊤, μ.HasNashEquilibrium] :=
  Impl.PayoffFunction.nashEquilibrium_tfae

section Lattice

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]

/-- Proposition 4.18. Semistability gives the reverse game-value inequality; either set of
first-mover hypotheses then gives Nash equilibrium. -/
theorem proposition_4_18 {S : Type*} [CompleteLinearOrder S]
    (μ : PayoffFunction ℒ S) (hμ : μ.IsSemistable) :
    μ.B ⊤ ≤ μ.A ⊤ ∧
      ((μ.WeakACC ∧ μ.WeakSlopeLikeAtTop) ∨ (μ.StrongDCC ∧ μ.WeakSlopeLikeAtBot) →
        μ.HasNashEquilibrium) :=
  ⟨Impl.PayoffFunction.IsSemistable.B_top_le_A_top hμ,
    Impl.PayoffFunction.IsSemistable.hasNashEquilibrium_of_firstMover hμ⟩

/-- Proposition 4.20. Nash equilibrium implies semistability when every initial restriction
satisfies the hypotheses of Proposition 4.1. -/
theorem proposition_4_20 (μ : PayoffFunction ℒ S)
    (h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) → (μ.restrict ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩).WeakACC)
    (h₂ : ∀ x : ℒ, (hx : x ≠ ⊥) →
      (μ.restrict ⟨⊥, x, bot_lt_iff_ne_bot.2 hx⟩).WeakSlopeLikeAtTop) :
    μ.HasNashEquilibrium → μ.IsSemistable :=
  Impl.PayoffFunction.isSemistable_of_hasNashEquilibrium h₁ h₂

/-- Theorem 4.21. Under both chain conditions and slope-likeness, the three extremal-payoff
equalities, Nash equilibrium and semistability are equivalent. -/
theorem theorem_4_21 {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)
    [μ.IsSlopeLike] [μ.WeakACC] [μ.StrongDCC] :
    List.TFAE [μ.max ⊤ = μ ⊤, μ.min ⊤ = μ ⊤, μ.min ⊤ = μ.max ⊤,
      μ.HasNashEquilibrium, μ.IsSemistable] :=
  Impl.PayoffFunction.nashEquilibrium_semistability_tfae

end Lattice

end HarderNarasimhan
