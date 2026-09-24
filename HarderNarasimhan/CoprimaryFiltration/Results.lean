/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.CoprimaryFiltration.Impl

/-!
# Coprimary filtrations: statements (Section 3.4)

All prime comparisons use the fixed linear extension of `PrimeSpectrum R`.
The structures in `Defs` express the chains and their successive quotients;
the proofs and canonical construction are in `Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open Coprimary Impl.Coprimary

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Proposition 3.11: the associated-prime payoff is convex. -/
theorem proposition_3_11 : (payoff R M).IsConvex := inferInstance

omit [Nontrivial M] in
/-- Proposition 3.12: the value on `N' < N` is the singleton containing the least
associated prime of `N / N'`. -/
theorem proposition_3_12 (I : StrictIntvl (Submodule R M)) :
    (payoff R M).A I =
      .principal (toColex {(subquotientAssociatedPrimes I).toFinset.min'
        (subquotientAssociatedPrimes_nonempty I)}) :=
  Impl.Coprimary.A_payoff I

omit [Nontrivial M] in
/-- Proposition 3.13: both the ascending and the `μA`-descending chain conditions hold. -/
theorem proposition_3_13 : WellFoundedGT (Submodule R M) ∧ (payoff R M).ADCC :=
  ⟨inferInstance, inferInstance⟩

/-- Remark 3.14: semistability is equivalent to the constant-value condition and to
having exactly one associated prime. -/
theorem remark_3_14 : List.TFAE [
    (payoff R M).IsSemistable,
    ∀ N : Submodule R M, (hN : ⊥ < N) → (payoff R M).A ⟨⊥, N, hN⟩ = (payoff R M).A ⊤,
    ∃! p, p ∈ associatedPrimes R M] :=
  Impl.Coprimary.semistability_tfae

/-- Theorem 3.15 (Theorem 1.2): there is a unique finite filtration with coprimary
successive quotients and strictly decreasing associated primes. -/
theorem theorem_3_15 : ∃! _F : CoprimaryFiltration R M, True :=
  ⟨Impl.Coprimary.coprimaryFiltration R M, trivial, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- Remark 3.16: the factor primes are exactly the associated primes of the module. -/
theorem remark_3_16 (F : CoprimaryFiltration R M) :
    associatedPrimes R M =
      ⋃ i < F.length, associatedPrimes R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) :=
  Impl.CoprimaryFiltration.associatedPrimes_eq_iUnion F

end HarderNarasimhan
