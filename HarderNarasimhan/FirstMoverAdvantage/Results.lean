/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.FirstMoverAdvantage.Impl

/-!
# Sections 4.1–4.2: first-mover advantage — statements

The two game-value formulas and the rank criterion; proofs are in `FirstMoverAdvantage.Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Proposition 4.1. Under the two ascending hypotheses, player A's value is the payoff infimum on
final intervals, and the first mover has an advantage. -/
theorem proposition_4_1 (μ : PayoffFunction ℒ S) [μ.WeakACC] [μ.WeakSlopeLikeAtTop] :
    μ.A ⊤ = μ.min ⊤ ∧ μ.A ⊤ ≤ μ.B ⊤ :=
  ⟨Impl.PayoffFunction.A_top_eq_min_top, Impl.PayoffFunction.A_top_le_B_top⟩

/-- Proposition 4.3. Under the two dual hypotheses, player B's value is the payoff supremum on
initial intervals, and the first mover has an advantage. The second hypothesis uses the actual
order dual of Proposition 4.1; see `PayoffFunction.WeakSlopeLikeAtBot` for the v1 discrepancy. -/
theorem proposition_4_3 (μ : PayoffFunction ℒ S) [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] :
    μ.B ⊤ = μ.max ⊤ ∧ μ.A ⊤ ≤ μ.B ⊤ :=
  ⟨Impl.PayoffFunction.B_top_eq_max_top, Impl.PayoffFunction.A_top_le_B_top_of_strongDCC⟩

omit [Nontrivial ℒ] in
/-- Remark 4.4. A monotone real rank with well-ordered image implies the strong descending chain
condition if every rank-constant interval has infinite payoff. -/
theorem remark_4_4 (μ : PayoffFunction ℒ S) (r : ℒ → ℝ) (hr₁ : Monotone r)
    (hr₂ : IsWellOrder (Set.range r) (· < ·))
    (h : ∀ I : StrictIntvl ℒ, r I.left = r I.right → μ I = ⊤) : μ.StrongDCC :=
  Impl.PayoffFunction.strongDCC_of_wellOrderedRank μ r hr₁ hr₂ h

end HarderNarasimhan
