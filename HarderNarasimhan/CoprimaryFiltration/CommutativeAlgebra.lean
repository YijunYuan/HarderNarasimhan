/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support

/-!
Auxiliary commutative algebra results for the coprimary filtration development.

Some commutative algebra facts used in `HarderNarasimhan.CoprimaryFiltration.Impl`
are formalized in this file with complete Lean proofs.

Keeping these lemmas isolated helps keep the filtration implementation readable and
lets downstream files reuse a stable commutative-algebra API.

API note: this file is an explicit collection of commutative-algebra lemmas used by the coprimary
filtration implementation. Downstream developments should avoid depending on it directly;
instead, import `HarderNarasimhan.CoprimaryFiltration.Results`.
-/

namespace HarderNarasimhan
namespace CommutativeAlgebra

/--
One-sided inclusion for associated primes of the kernel of the localization map.

If `p ∈ associatedPrimes R (ker (mkLinearMap S M))`, then `p` is an associated prime of `M`
and `p` is **not** disjoint from the multiplicative set `S`.

This is one direction of `associatedPrimes_ker_mkLinearMap_eq`.
-/
lemma associatedPrimes_ker_mkLinearMap_subset
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) ⊆
    (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
  intro p hp
  refine ⟨associatedPrimes.subset_of_injective (Submodule.injective_subtype _) hp, ?_⟩
  intro hpempty
  obtain ⟨hpPrime, x, hx⟩ := hp
  obtain ⟨r, hrS, hrx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x.1)).1 x.2
  have hrp : r ∈ p := by
    rw [hx, Ideal.mem_radical_iff]
    exact ⟨1, by simpa [Submodule.mem_colon_singleton, Subtype.ext_iff] using hrx⟩
  exact Set.Nonempty.ne_empty (⟨r, hrp, hrS⟩ : (p.carrier ∩ S).Nonempty) hpempty.2

/-- If `p` is an associated prime of `M` and `p` meets the multiplicative set `S`,
then `p` is an associated prime of the kernel of the localization map
`mkLinearMap S M : M →ₗ[R] LocalizedModule S M`.

This is the “meets `S`” direction used to identify associated primes of
`ker (mkLinearMap S M)` with the associated primes of `M` that are *not* disjoint from `S`.
-/
lemma mem_associatedPrimes_ker_mkLinearMap_of_mem_associatedPrimes_of_inter_nonempty
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) {p : Ideal R}
(hp : p ∈ associatedPrimes R M) (hinter : (p.carrier ∩ S).Nonempty) :
  p ∈ associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) := by
  obtain ⟨hpPrime, y, hy⟩ := (isAssociatedPrime_iff (R := R) (M := M)).mp hp
  obtain ⟨r, hrp, hrS⟩ := hinter
  have hry : r • y = 0 := by simpa [hy, Submodule.mem_colon_singleton] using hrp
  have hyker : y ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M) :=
    (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := y)).2 ⟨r, hrS, hry⟩
  refine (isAssociatedPrime_iff (R := R) (M := LinearMap.ker (LocalizedModule.mkLinearMap S M))).2
    ⟨hpPrime, ⟨y, hyker⟩, ?_⟩
  rw [hy]
  ext z
  simp [Submodule.mem_colon_singleton, Subtype.ext_iff]

/--
Associated primes of the kernel of the localization map.

This identifies the associated primes of
`ker (LocalizedModule.mkLinearMap S M) : Submodule R M` with the associated primes of `M`
that *do* meet the multiplicative set `S`.

Equivalently, these are the associated primes of `M` after removing those disjoint from `S`.
This lemma is used as the “kernel part” in the classical splitting of associated primes under
localization.
-/
lemma associatedPrimes_ker_mkLinearMap_eq
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) =
    (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
  refine le_antisymm (associatedPrimes_ker_mkLinearMap_subset (S := S)) fun p hp ↦
    mem_associatedPrimes_ker_mkLinearMap_of_mem_associatedPrimes_of_inter_nonempty _ hp.1
      (Set.nonempty_iff_ne_empty.mpr fun h ↦ hp.2 ⟨hp.1, h⟩)

/--
Associated primes disjoint from `S` survive in the localization quotient.

If `p` is an associated prime of `M` and `p.carrier ∩ S = ∅`, then `p` is an associated prime of
the quotient `M ⧸ ker(mkLinearMap S M)`.

This is the “disjoint part” inclusion used in the splitting of associated primes under
localization.
-/
lemma disjoint_associatedPrimes_subset_associatedPrimes_quot_ker_mkLinearMap
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } ⊆
    associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)) := by
  intro p hp
  exact Or.resolve_left
    (associatedPrimes.subset_union_of_exact (Submodule.injective_subtype _)
      (LinearMap.exact_subtype_mkQ (LinearMap.ker (LocalizedModule.mkLinearMap S M))) hp.1)
    fun hpKer ↦ (associatedPrimes_ker_mkLinearMap_subset S hpKer).2 hp

/--
Associated primes of a localized module are disjoint from the multiplicative set.

More precisely, if `p ∈ associatedPrimes R (LocalizedModule S M)`, then `p.carrier ∩ S = ∅`.
This is a standard fact in commutative algebra: an element of `S` becomes a unit after
localization, so no associated prime of the localized module can contain an element of `S`.
-/
lemma associatedPrimes_localizedModule_subset_disjoint
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  associatedPrimes R (LocalizedModule S M) ⊆ { p : Ideal R | p.carrier ∩ S = ∅ } := by
  rintro p ⟨hpPrime, x, hx⟩
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨r, hrp, hrS⟩
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hx ▸ hrp)
  have hx0 : x = 0 :=
    IsLocalizedModule.smul_injective (f := LocalizedModule.mkLinearMap S M) ⟨r ^ n, pow_mem hrS n⟩
      (by simpa [Submonoid.smul_def, Submodule.mem_colon_singleton] using hn)
  exact hpPrime.ne_top (hx.trans (by rw [hx0, Submodule.colon_singleton_zero, Ideal.radical_top]))

/--
Associated primes of the localization quotient are disjoint from the multiplicative set.

More precisely, any `p ∈ associatedPrimes R (M ⧸ ker(mkLinearMap S M))` satisfies
`p.carrier ∩ S = ∅`.

In this file this is used as a “black box” input in the Bourbaki-style splitting of
associated primes under localization.
-/
lemma associatedPrimes_quot_ker_mkLinearMap_subset_disjoint
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)) ⊆
    { p : Ideal R | p.carrier ∩ S = ∅ } := by
  let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
  have hfQ : Function.Injective (K.liftQ (LocalizedModule.mkLinearMap S M) le_rfl) :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' K (LocalizedModule.mkLinearMap S M) rfl)
  exact fun p hp ↦ associatedPrimes_localizedModule_subset_disjoint (S := S)
    (associatedPrimes.subset_of_injective hfQ hp)

open Module in
/--
If `p` is an associated prime of the quotient `M ⧸ ker(mkLinearMap S M)` and `p` is disjoint
from the multiplicative set `S`, then `p` is already an associated prime of `M`.

This lemma is used to identify the “disjoint part” of the associated primes of `M` with the
associated primes of the localization quotient.
-/
lemma mem_associatedPrimes_of_mem_associatedPrimes_quot_ker_mkLinearMap_of_disjoint
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) {p : Ideal R}
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
Minimal associated primes correspond to minimal elements of the support.

Reference: Stacks Project, tag `02CE`.
-/
@[stacks 02CE]
lemma min_associated_prime_iff_min_supp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : PrimeSpectrum R} :
Minimal (fun J ↦ J ∈ associatedPrimes R M) I.asIdeal ↔ Minimal (fun J ↦ J ∈ Module.support R M) I
:= by
  constructor
  · intro hI
    refine ⟨(Module.mem_support_iff_of_finite (R := R) (M := M)).2
      (Submodule.annihilator_top (R := R) (M := M) ▸
        IsAssociatedPrime.annihilator_le (M := M) (I := I.asIdeal) hI.1), ?_⟩
    intro J hJ hJI
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (J := J.asIdeal)
      ((Module.mem_support_iff_of_finite (R := R) (M := M)).1 hJ)
    have hpAss : p ∈ associatedPrimes R M :=
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (R := R) (M := M) hp
    exact (hI.eq_of_ge hpAss <| hpJ.trans hJI).trans_le hpJ
  · intro hI
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp, hpI⟩ := Ideal.exists_minimalPrimes_le (J := I.asIdeal)
        ((Module.mem_support_iff_of_finite (R := R) (M := M)).1 hI.1)
      have hpSupp : (⟨p, hp.1.1⟩ : PrimeSpectrum R) ∈ Module.support R M :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).2 hp.1.2
      have hpEqI : p = I.asIdeal := congrArg PrimeSpectrum.asIdeal (hI.eq_of_ge hpSupp hpI).symm
      exact hpEqI ▸
        Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          (R := R) (M := M) hp
    · intro J hJ hJI
      have hJSupp : (⟨J, hJ.1⟩ : PrimeSpectrum R) ∈ Module.support R M :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).2
          (Submodule.annihilator_top (R := R) (M := M) ▸
            IsAssociatedPrime.annihilator_le (M := M) (I := J) hJ)
      exact hI.2 hJSupp hJI

open Module in
/--
Associated primes under localization, characterized by the kernel of the localization map.

This packages a classical statement (Bourbaki, *Algèbre commutative*, Ch. IV, §1,
no. 2, Prop. 6) describing how associated primes split between a submodule and its
quotient when localizing at a multiplicative set `S`.
-/
lemma bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) (N : Submodule R M) :
  (associatedPrimes R N) =
    (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } ∧
  (associatedPrimes R (M⧸N)) = { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ }
↔ N = LinearMap.ker (LocalizedModule.mkLinearMap S M)
:= by
  constructor
  · intro hAss
    let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
    have hNoDisjAssN : ∀ p ∈ associatedPrimes R N, p.carrier ∩ S ≠ ∅ := fun p hpN hpDisj ↦
      have hpDiff := hAss.1.subset hpN
      hpDiff.2 ⟨hpDiff.1, hpDisj⟩
    have hLocAssEmpty : associatedPrimes (Localization S) (LocalizedModule S N) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun q hq ↦ ?_
      open Module.associatedPrimes in
      have hqComap : Ideal.comap (algebraMap R (Localization S)) q ∈ associatedPrimes R N :=
        comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
          S (LocalizedModule.mkLinearMap S N) q hq
          ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› _)
      have hqDisj : (Ideal.comap (algebraMap R (Localization S)) q).carrier ∩ S = ∅ := by
        simpa [Set.inter_comm] using Set.disjoint_iff_inter_eq_empty.mp
          ((IsLocalization.disjoint_under_iff S (Localization S) q).mpr hq.1.ne_top)
      exact hNoDisjAssN _ hqComap hqDisj
    have hSubLocN : Subsingleton (LocalizedModule S N) := by
      by_contra hns
      have : Nontrivial (LocalizedModule S N) := not_subsingleton_iff_nontrivial.mp hns
      obtain ⟨q, hq⟩ := associatedPrimes.nonempty (Localization S) (LocalizedModule S N)
      exact Set.notMem_empty q (hLocAssEmpty ▸ hq)
    have hNleK : N ≤ K := by
      intro x hxN
      obtain ⟨s, hsS, hsxN⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff
        (S := S) (m := (⟨x, hxN⟩ : N))).1 (LinearMap.mem_ker.mpr (Subsingleton.elim _ _))
      exact (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).2
        ⟨s, hsS, congrArg Subtype.val hsxN⟩
    have hKleN : K ≤ N := by
      intro x hxK
      by_contra hxN
      obtain ⟨p, hpMN, hple⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R (N.mkQ x)
        (by simpa [Submodule.Quotient.mk_eq_zero] using hxN)
      have hpDisj : p.carrier ∩ S = ∅ := (hAss.2.subset hpMN).2
      obtain ⟨s, hsS, hsx⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).1 hxK
      have hsP : s ∈ p := hple (by
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_smul, hsx, map_zero])
      exact Set.notMem_empty s (hpDisj ▸ ⟨hsP, hsS⟩)
    exact le_antisymm hNleK hKleN
  · rintro rfl
    refine ⟨associatedPrimes_ker_mkLinearMap_eq (S := S), le_antisymm (fun p hp ↦ ?_)
      (disjoint_associatedPrimes_subset_associatedPrimes_quot_ker_mkLinearMap (S := S))⟩
    have hpDisj := associatedPrimes_quot_ker_mkLinearMap_subset_disjoint (S := S) hp
    exact ⟨mem_associatedPrimes_of_mem_associatedPrimes_quot_ker_mkLinearMap_of_disjoint
      (S := S) hp hpDisj, hpDisj⟩

end CommutativeAlgebra
end HarderNarasimhan
