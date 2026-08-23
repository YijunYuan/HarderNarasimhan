/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
Auxiliary commutative algebra for the coprimary filtration development.

The single fact needed by `HarderNarasimhan.CoprimaryFiltration.Impl` is the quotient half of
Bourbaki, *Algèbre commutative*, Ch. IV, §1, no. 2, Prop. 6: writing `K` for the kernel of the
localization map `M →ₗ[R] S⁻¹M`, the associated primes of `M ⧸ K` are exactly the associated
primes of `M` that are disjoint from `S` (`associatedPrimes_quot_ker_mkLinearMap`).

The proof splits into three observations:

* every associated prime of `K` meets `S` (elements of `K` are `S`-torsion);
* every associated prime of `M ⧸ K` is disjoint from `S` (since `M ⧸ K` embeds into `S⁻¹M`,
  where `S` acts injectively);
* conversely, an associated prime of `M ⧸ K` disjoint from `S` is an associated prime of `M`
  (localize at that prime: `K` localizes to zero).

API note: this file is internal to the coprimary filtration implementation. Downstream
developments should import `HarderNarasimhan.CoprimaryFiltration.Results` instead.
-/

namespace HarderNarasimhan
namespace CommutativeAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (S : Submonoid R)

/--
Every associated prime of the kernel of the localization map meets `S`.

Indeed, any element of the kernel is `S`-torsion, so the (radical) annihilator ideal defining
the associated prime contains an element of `S`.
-/
lemma meets_of_mem_associatedPrimes_ker {p : Ideal R}
    (hp : p ∈ associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M))) :
    (p.carrier ∩ S).Nonempty := by
  obtain ⟨hpPrime, x, hx⟩ := hp
  obtain ⟨r, hrS, hrx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x.1)).1 x.2
  refine ⟨r, show r ∈ p from ?_, hrS⟩
  rw [hx, Ideal.mem_radical_iff]
  exact ⟨1, by simpa [Submodule.mem_colon_singleton, Subtype.ext_iff] using hrx⟩

/--
Associated primes of a localized module (viewed over the base ring) are disjoint from the
multiplicative set: elements of `S` act injectively on `S⁻¹M`.
-/
lemma inter_eq_empty_of_mem_associatedPrimes_localizedModule {p : Ideal R}
    (hp : p ∈ associatedPrimes R (LocalizedModule S M)) : p.carrier ∩ S = ∅ := by
  obtain ⟨hpPrime, x, hx⟩ := hp
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨r, hrp, hrS⟩
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hx ▸ hrp)
  have hx0 : x = 0 :=
    IsLocalizedModule.smul_injective (f := LocalizedModule.mkLinearMap S M) ⟨r ^ n, pow_mem hrS n⟩
      (by simpa [Submonoid.smul_def, Submodule.mem_colon_singleton] using hn)
  exact hpPrime.ne_top (hx.trans (by rw [hx0, Submodule.colon_singleton_zero, Ideal.radical_top]))

/--
Associated primes of `M ⧸ ker(M → S⁻¹M)` are disjoint from `S`, since the quotient embeds
into the localized module.
-/
lemma inter_eq_empty_of_mem_associatedPrimes_quot_ker {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M))) :
    p.carrier ∩ S = ∅ := by
  have hfQ : Function.Injective ((LinearMap.ker (LocalizedModule.mkLinearMap S M)).liftQ
      (LocalizedModule.mkLinearMap S M) le_rfl) :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ rfl)
  exact inter_eq_empty_of_mem_associatedPrimes_localizedModule S
    (associatedPrimes.subset_of_injective hfQ hp)

open Module in
/--
An associated prime of `M ⧸ ker(M → S⁻¹M)` that is disjoint from `S` is an associated prime
of `M`.

The proof localizes at `p`: the kernel localizes to zero (its elements are `S`-torsion and `S`
consists of units in `R_p`), so `(M ⧸ K)_p ≅ M_p`, and associated primes transfer through the
localization at a prime.
-/
lemma mem_associatedPrimes_of_mem_associatedPrimes_quot_ker [IsNoetherianRing R] {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)))
    (hpDisj : p.carrier ∩ S = ∅) :
    p ∈ associatedPrimes R M := by
  have : p.IsPrime := hp.1
  let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
  have hKloc : K.localized (p := p.primeCompl) = ⊥ := by
    change Submodule.localized' (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) K = ⊥
    rw [Submodule.localized'_eq_span]
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hsS, hsx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).1 hx
    have hsP : s ∈ p.primeCompl := fun hsp => Set.notMem_empty s (hpDisj ▸ ⟨hsp, hsS⟩)
    exact LinearMap.mem_ker.mp
      ((LocalizedModule.mem_ker_mkLinearMap_iff (S := p.primeCompl) (m := x)).2 ⟨s, hsP, hsx⟩)
  let e : LocalizedModule p.primeCompl (M ⧸ K) ≃ₗ[Localization p.primeCompl]
      LocalizedModule p.primeCompl M :=
    (localizedQuotientEquiv (p := p.primeCompl) (M' := K)).symm.trans
      (Submodule.quotEquivOfEqBot _ hKloc)
  have hAtPrimeQuot : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p (M ⧸ K)) := by
    simpa [LocalizedModule.AtPrime, K] using
      (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes
        (R := R) (M := (M ⧸ K)) (p := p) hp)
  have hAtPrimeM : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    simpa [LocalizedModule.AtPrime, K] using
      ((LinearEquiv.AssociatedPrimes.eq (R := Localization.AtPrime p) e) ▸ hAtPrimeQuot)
  have hComap :=
    associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) _ hAtPrimeM
      ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› _)
  simpa [Localization.AtPrime.under_maximalIdeal] using hComap

/--
The quotient half of Bourbaki, *Algèbre commutative*, Ch. IV, §1, no. 2, Prop. 6: the
associated primes of `M ⧸ ker(M → S⁻¹M)` are exactly the associated primes of `M` that are
disjoint from `S`.
-/
theorem associatedPrimes_quot_ker_mkLinearMap [IsNoetherianRing R] :
    associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)) =
      { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
  refine le_antisymm
    (fun p hp ↦ ⟨mem_associatedPrimes_of_mem_associatedPrimes_quot_ker S hp
      (inter_eq_empty_of_mem_associatedPrimes_quot_ker S hp),
      inter_eq_empty_of_mem_associatedPrimes_quot_ker S hp⟩)
    fun p hp ↦ Or.resolve_left
      (associatedPrimes.subset_union_of_exact (Submodule.injective_subtype _)
        (LinearMap.exact_subtype_mkQ (LinearMap.ker (LocalizedModule.mkLinearMap S M))) hp.1)
      fun hpKer ↦ (meets_of_mem_associatedPrimes_ker S hpKer).ne_empty hp.2

end CommutativeAlgebra
end HarderNarasimhan
