/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Impl

/-!
# Section 3.3: Harder–Narasimhan filtration

Paper statements for Definition 3.9 and Theorem 3.10. Their constructions and proofs,
including the relation-series formulations, are in `Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*}

/-- Definition 3.9: under hypotheses (a)–(c), the Harder–Narasimhan filtration exists.
Its steps are semistable and successive `μ.A`-values satisfy `¬ aᵢ ≤ aᵢ₊₁`. -/
theorem definition_3_9 [CompleteLattice S] (μ : PayoffFunction ℒ S)
    [μ.IsConvex] [μ.ADCC] [μ.Admissible] : Nonempty μ.HarderNarasimhanFiltration :=
  ⟨Impl.PayoffFunction.hnFiltration μ⟩

/-- Theorem 3.10: a strictly increasing filtration with semistable steps and strictly
decreasing `μ.A`-values coincides with the canonical Harder–Narasimhan filtration. -/
theorem theorem_3_10 [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)
    [μ.IsConvex] [μ.ADCC] (F : μ.HarderNarasimhanFiltration) :
    F = Impl.PayoffFunction.hnFiltration μ :=
  Subsingleton.elim _ _

end HarderNarasimhan
