/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolderFiltration.Impl

/-!
# Section 4.5: Jordan–Hölder filtration

The existence statement of Theorem 4.25 and the length assertion of Remark 4.26.
Definitions are in `Defs`; all constructions and proofs are in `Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)
variable [μ.FiniteTotalPayoff] [μ.IsSlopeLike] [μ.IsSemistable] [μ.EventuallyTopDCC]

/-- Theorem 4.25: there is a finite strictly decreasing chain from `⊤` to `⊥` with
constant total payoff and the strict payoff inequality on each intermediate point. -/
theorem theorem_4_25 :
    ∃ (n : ℕ) (y : ℕ → ℒ), y 0 = ⊤ ∧ y n = ⊥ ∧
      ∃ hy : StrictAntiOn y (Set.Iic n), ∀ i, (hi : i < n) →
        μ ⟨y (i + 1), y i, hy hi.le hi (lt_add_one i)⟩ = μ ⊤ ∧
        ∀ z, (hz : y (i + 1) < z) → z < y i →
          μ ⟨y (i + 1), z, hz⟩ < μ ⟨y (i + 1), y i, hy hi.le hi (lt_add_one i)⟩ :=
  Impl.PayoffFunction.exists_jordanHolder_sequence μ

/-- Remark 4.26: Jordan–Hölder filtrations have the same length for an affine payoff.
The formalization assumes a modular lattice, as used in the join argument. -/
theorem remark_4_26 [IsModularLattice ℒ] [μ.IsAffine] (F G : μ.JordanHolderFiltration) :
    F.length = G.length :=
  Impl.PayoffFunction.JordanHolderFiltration.length_eq F G

end HarderNarasimhan
