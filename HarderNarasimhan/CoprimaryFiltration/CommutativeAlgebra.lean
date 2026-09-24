/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Associated primes of the quotient by a localization kernel

Let `M` be a module over a commutative Noetherian ring `R`, let `S` be a multiplicative
subset of `R`, and let `K` be the kernel of the localization map `M → S⁻¹M`.
The associated primes of `M ⧸ K` are exactly the associated primes of `M` disjoint from `S`.

This result is used to compute the value when player A moves first in
`HarderNarasimhan/CoprimaryFiltration/Impl.lean`.

## Main results

* `HarderNarasimhan.associatedPrimes_quot_ker_mkLinearMap`: the associated primes of
  `M ⧸ ker (M → S⁻¹M)` are exactly the associated primes of `M` disjoint from `S`.
* `HarderNarasimhan.associatedPrimes_subset_of_submoduleOf_le`: for submodules `A ≤ B`,
  every associated prime of `A / (A ∩ N)` is an associated prime of `B / (B ∩ N)`.

## References

* [N. Bourbaki, *Algèbre commutative*][bourbaki1985]
-/

@[expose] public section

namespace HarderNarasimhan

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Commutative algebra input for Proposition 3.12. For submodules `N`, `A`, and `B` with `A ≤ B`,
every associated prime of
`A / (A ∩ N)` is an associated prime of `B / (B ∩ N)`. -/
lemma associatedPrimes_subset_of_submoduleOf_le (N A B : Submodule R M) (h : A ≤ B) :
    associatedPrimes R (↥A ⧸ N.submoduleOf A) ⊆ associatedPrimes R (↥B ⧸ N.submoduleOf B) := by
  have hcomap : Submodule.comap (Submodule.inclusion h) (N.submoduleOf B) = N.submoduleOf A := rfl
  refine associatedPrimes.subset_of_injective
    (f := (N.submoduleOf A).mapQ (N.submoduleOf B) (Submodule.inclusion h) (le_of_eq hcomap.symm))
    ?_
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]

variable (S : Submonoid R)

/-- Commutative algebra input for Proposition 3.12. Every associated prime of the kernel of the
localization map `M → S⁻¹M` meets `S`. -/
lemma inter_nonempty_of_mem_associatedPrimes_ker {p : Ideal R}
    (hp : p ∈ associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M))) :
    (p.carrier ∩ S).Nonempty := by
  obtain ⟨hpPrime, x, hx⟩ := hp
  obtain ⟨r, hrS, hrx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x.1)).1 x.2
  refine ⟨r, show r ∈ p from ?_, hrS⟩
  rw [hx, Ideal.mem_radical_iff]
  exact ⟨1, by simpa [Submodule.mem_colon_singleton, Subtype.ext_iff] using hrx⟩

/-- Commutative algebra input for Proposition 3.12. The associated primes of `S⁻¹M`, viewed as an
`R`-module, are disjoint from `S`. -/
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

/-- Commutative algebra input for Proposition 3.12. The associated primes of `M ⧸ ker (M → S⁻¹M)`
are disjoint from `S`. -/
lemma inter_eq_empty_of_mem_associatedPrimes_quot_ker {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M))) :
    p.carrier ∩ S = ∅ := by
  apply inter_eq_empty_of_mem_associatedPrimes_localizedModule (M := M) S
  apply associatedPrimes.subset_of_injective (f :=
    (LinearMap.ker (LocalizedModule.mkLinearMap S M)).liftQ
      (LocalizedModule.mkLinearMap S M) le_rfl) ?_ hp
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ rfl)

open Module in
/-- Commutative algebra input for Proposition 3.12. Over a Noetherian ring, an associated prime of
`M ⧸ ker (M → S⁻¹M)` disjoint from `S`
is an associated prime of `M`. -/
lemma mem_associatedPrimes_of_mem_associatedPrimes_quot_ker [IsNoetherianRing R] {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)))
    (hpDisj : p.carrier ∩ S = ∅) :
    p ∈ associatedPrimes R M := by
  let : p.IsPrime := hp.1
  let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
  -- Every element of the kernel is killed by a unit after localization at `p`.
  have hKloc : K.localized (p := p.primeCompl) = ⊥ := by
    change Submodule.localized' (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) K = ⊥
    rw [Submodule.localized'_eq_span]
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hsS, hsx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).1 hx
    have hsP : s ∈ p.primeCompl := fun hsp ↦ Set.notMem_empty s (hpDisj ▸ ⟨hsp, hsS⟩)
    exact LinearMap.mem_ker.mp
      ((LocalizedModule.mem_ker_mkLinearMap_iff (S := p.primeCompl) (m := x)).2 ⟨s, hsP, hsx⟩)
  let e : LocalizedModule p.primeCompl (M ⧸ K) ≃ₗ[Localization p.primeCompl]
      LocalizedModule p.primeCompl M :=
    (localizedQuotientEquiv (p := p.primeCompl) (M' := K)).symm.trans
      (Submodule.quotEquivOfEqBot _ hKloc)
  -- Transfer the associated prime through the localized quotient isomorphism.
  have hAtPrimeM : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    rw [← LinearEquiv.AssociatedPrimes.eq (R := Localization.AtPrime p) e]
    exact Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  -- Contract back to `R`; finite generation is supplied by Noetherianity.
  simpa [Localization.AtPrime.under_maximalIdeal] using
    (associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) _ hAtPrimeM
      ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› _))

/-- Commutative algebra input for Proposition 3.12. Over a Noetherian ring, the associated primes
of `M ⧸ ker (M → S⁻¹M)` are exactly
the associated primes of `M` disjoint from `S`. -/
theorem associatedPrimes_quot_ker_mkLinearMap [IsNoetherianRing R] :
    associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)) =
      { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
  apply Set.Subset.antisymm
  · intro p hp
    have hdisj := inter_eq_empty_of_mem_associatedPrimes_quot_ker S hp
    exact ⟨mem_associatedPrimes_of_mem_associatedPrimes_quot_ker S hp hdisj, hdisj⟩
  · rintro p ⟨hp, hdisj⟩
    rcases associatedPrimes.subset_union_of_exact (Submodule.injective_subtype _)
      (LinearMap.exact_subtype_mkQ (LinearMap.ker (LocalizedModule.mkLinearMap S M))) hp with
      hpKer | hpQuot
    · exact ((inter_nonempty_of_mem_associatedPrimes_ker S hpKer).ne_empty hdisj).elim
    · exact hpQuot

end HarderNarasimhan
