/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support

/-!
Admitted auxiliary results for the coprimary filtration development.

Some commutative algebra facts used in `HarderNarasimhan.CoprimaryFiltration.Impl`
are currently treated as black boxes. The lemmas in this file are stated with their
intended meaning and references, but their proofs are `admit`.

Keeping these assumptions isolated makes it easy to track what remains to be
formalized.

API note: this file is an explicit collection of admitted lemmas used by the coprimary
filtration implementation. Downstream developments should avoid depending on it directly;
instead, import `HarderNarasimhan.CoprimaryFiltration.Results`.
-/

namespace HarderNarasimhan
namespace AdmittedResults


/-
Minimal associated primes correspond to minimal elements of the support.

Reference: Stacks Project, tag `02CE`.

Currently admitted.
-/
@[stacks 02CE]
lemma min_associated_prime_iff_min_supp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : PrimeSpectrum R} :
Minimal (fun J ↦ J ∈ associatedPrimes R M) I.asIdeal ↔ Minimal (fun J ↦ J ∈ Module.support R M) I
:= by admit

/-
Associated primes under localization, characterized by the kernel of the localization map.

This packages a classical statement (Bourbaki, *Algèbre commutative*, Ch. IV, §1,
no. 2, Prop. 6) describing how associated primes split between a submodule and its
quotient when localizing at a multiplicative set `S`.

Currently admitted.
-/
lemma bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) (N : Submodule R M) :
  (associatedPrimes R N) =
    (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } ∧
  (associatedPrimes R (M⧸N)) = { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ }
↔ N = LinearMap.ker (LocalizedModule.mkLinearMap S M)
:= by admit

end AdmittedResults
end HarderNarasimhan
