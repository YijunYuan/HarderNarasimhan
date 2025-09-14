import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support

namespace HarderNarasimhan
namespace AdmittedResults


@[stacks 02CE]
lemma min_associated_prime_iff_min_supp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : PrimeSpectrum R} :
Minimal (fun J ↦ J ∈ associatedPrimes R M) I.asIdeal ↔ Minimal (fun J ↦ J ∈ Module.support R M) I := by admit

lemma bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) (N : Submodule R M) :
  (associatedPrimes R N) = (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } ∧
  (associatedPrimes R (M⧸N)) = { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ }
↔ N = LinearMap.ker (LocalizedModule.mkLinearMap S M)
:= by admit

end AdmittedResults
end HarderNarasimhan
