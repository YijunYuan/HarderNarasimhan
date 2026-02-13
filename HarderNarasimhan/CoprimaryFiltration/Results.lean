/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.CoprimaryFiltration.Impl

/-!
Public-facing results for coprimary filtrations.

The internal file `HarderNarasimhan.CoprimaryFiltration.Impl` contains the main
constructions and commutative algebra arguments. Here we restate and re-export the
key theorems/lemmas under names aligned with the project’s numbering.

API overview:

* This is the recommended import for users who want the coprimary filtration interface and its
  connections to Harder–Narasimhan filtrations.
* The underlying constructions live in `HarderNarasimhan.CoprimaryFiltration.Impl`.
-/

namespace HarderNarasimhan

/-
Nonemptiness of the associated-primes finset for any strict interval.

This is used to define `Finset.min'` (and hence `μA`) for the slope built from
associated primes.
-/
lemma μ_nonempty {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty
------------
:= impl.μ_nonempty

/-
`μmax` does not change the slope `μ`.

The definition of `μ` already produces the maximal element in the relevant
construction, so `μmax (μ R M) I = μ R M I` for all intervals `I`.
-/
lemma μmax_eq_μ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2},
  μmax (μ R M) I = (μ R M) I
------------
:= impl.μmax_eq_μ

/-
Proposition 3.11: convexity of the slope `μ R M`.

Internally we build a `ConvexI TotIntvl` instance and then translate it to the
global `Convex` predicate.
-/
instance proposition_3_11 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Convex (μ R M)
------------
:= by
  apply (impl.ConvexI_TotIntvl_iff_Convex _).1
  infer_instance


/-
Proposition 3.12: explicit computation of `μA` for `μ R M`.

The `μA` value on an interval is the singleton containing the minimal associated
prime (in the `S₀ R` order) of the quotient corresponding to that interval.
-/
lemma proposition_3_12 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2},
  μA (μ R M) I = ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R)
------------
:= impl.prop3d12

/-
Proposition 3.13: well-foundedness and descending chain condition.

These two hypotheses are exactly what the general filtration existence theorem
requires.
-/
lemma proposition_3_13 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
WellFoundedGT (ℒ R M) ∧
μA_DescendingChainCondition (μ R M)
------------
:= ⟨inferInstance,inferInstance⟩

/-
Remark 3.14: a `TFAE` package of equivalent statements.
It lets you replace semistability of `μ R M` with the uniqueness-of-associated-prime condition.

The internal development shows:

* semistability of `μ R M`,
* a constant formula for `μA` on all nontrivial submodules, and
* uniqueness of the associated prime of `M`

are all equivalent.

API note: this lemma is a convenient gateway for users.
-/
lemma remark_3_14 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
List.TFAE [
Semistable (μ R M),
∀ N : (ℒ R M), (hN : ⊥ < N) →
  μA (μ R M) ⟨(⊥,N),hN⟩ = ({(((_μ R M) ⟨(⊥,⊤),bot_lt_top⟩).toFinset.min' (μ_nonempty _))} : S₀ R),
∃! p, p ∈ associatedPrimes R M
]
------------
:= by
  tfae_have 1 ↔ 2 := impl.rmk4d14₁
  tfae_have 1 ↔ 3 := impl.rmk4d14₂
  tfae_finish

/-
Theorem 3.15 (existence): there exists a coprimary filtration.

API note: this is the canonical existence statement for the coprimary chapter.
-/
instance theorem_3_15₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Nonempty (CoprimaryFiltration R M)
------------
:= inferInstance

/-
Theorem 3.15 (uniqueness): the coprimary filtration is unique.
This is derived from the uniqueness of the underlying Harder–Narasimhan filtration
when the codomain order is linear.

API note: when applicable, this lets you treat `CoprimaryFiltration R M` as a canonical object.
-/
noncomputable
instance theorem_3_15₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Unique (CoprimaryFiltration R M)
------------
:= inferInstance

end HarderNarasimhan
