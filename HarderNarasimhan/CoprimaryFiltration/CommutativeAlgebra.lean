/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
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
  refine ⟨?_, ?_⟩
  · exact associatedPrimes.subset_of_injective (R := R)
      (f := (LinearMap.ker (LocalizedModule.mkLinearMap S M)).subtype)
      (Submodule.injective_subtype _) hp
  · intro hpempty
    rcases hp with ⟨hpPrime, x, hx⟩
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x.1)).1 x.2 with ⟨r, hrS, hrx⟩
    have hrx' : r • x = 0 := Subtype.ext (by simpa using hrx)
    have hrp : r ∈ p := by
      rw [hx]
      simp only [Submodule.mem_colon_singleton, hrx', zero_mem]
    have hnonempty : (p.carrier ∩ S).Nonempty := ⟨r, hrp, hrS⟩
    exact hnonempty.ne_empty hpempty.2

/-- If `p` is an associated prime of `M` and `p` meets the multiplicative set `S`,
then `p` is an associated prime of the kernel of the localization map
`mkLinearMap S M : M →ₗ[R] LocalizedModule S M`.

This is the “meets `S`” direction used to identify associated primes of
`ker (mkLinearMap S M)` with the associated primes of `M` that are *not* disjoint from `S`.
-/
lemma mem_associatedPrimes_ker_mkLinearMap_of_mem_associatedPrimes_of_inter_nonempty
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) {p : Ideal R}
(hp : p ∈ associatedPrimes R M) (hinter : (p.carrier ∩ S).Nonempty) :
  p ∈ associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) := by
  rcases hp with ⟨hpPrime, y, hy⟩
  rcases hinter with ⟨r, hrp, hrS⟩
  have hry : r • y = 0 := by
    rw [hy] at hrp
    simpa [Submodule.mem_colon_singleton] using hrp
  have hyker : y ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M) := by
    rw [LinearMap.mem_ker]
    exact (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := y)).2 ⟨r, hrS, hry⟩
  refine ⟨hpPrime, ⟨y, hyker⟩, ?_⟩
  ext z
  constructor
  · intro hz
    rw [hy] at hz
    simpa [Submodule.mem_colon_singleton] using hz
  · intro hz
    rw [hy]
    simpa [Submodule.mem_colon_singleton] using hz

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
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(S : Submonoid R) :
  associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) =
    (associatedPrimes R M) \ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
  refine le_antisymm (associatedPrimes_ker_mkLinearMap_subset (S := S)) ?_
  intro p hp
  have hpNE : (p.carrier ∩ S).Nonempty := by
    by_contra h
    exact hp.2 ⟨hp.1, Set.not_nonempty_iff_eq_empty.mp h⟩
  exact mem_associatedPrimes_ker_mkLinearMap_of_mem_associatedPrimes_of_inter_nonempty _ hp.1 hpNE

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
  have hpNotKer : p ∉ associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) := by
    intro hpKer
    exact (associatedPrimes_ker_mkLinearMap_subset S hpKer).2 hp
  let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
  have hsubset : associatedPrimes R M ⊆ associatedPrimes R ↥K ∪ associatedPrimes R (M ⧸ K) :=
    associatedPrimes.subset_union_of_exact (R := R)
      (f := (K.subtype : K →ₗ[R] M))
      (g := (K.mkQ : M →ₗ[R] (M ⧸ K)))
      (Submodule.injective_subtype K)
      (LinearMap.exact_subtype_mkQ K)
  have hpUnion : p ∈
      associatedPrimes R (LinearMap.ker (LocalizedModule.mkLinearMap S M)) ∪
      associatedPrimes R (M ⧸ LinearMap.ker (LocalizedModule.mkLinearMap S M)) :=
    by
      simpa [K] using hsubset hp.1
  rcases hpUnion with hpKer | hpQuot
  · exact (hpNotKer hpKer).elim
  · exact hpQuot

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
  intro p hp
  rcases hp with ⟨hpPrime, x, hx⟩
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  rcases hne with ⟨r, hrp, hrS⟩
  have hrxR : (r : R) • x = 0 := by
    rw [hx] at hrp
    simpa [Submodule.mem_colon_singleton] using hrp
  have hrxS : (⟨r, hrS⟩ : S) • x = 0 := by simpa [Submonoid.smul_def] using hrxR
  have hx0 : x = 0 := by
    apply (IsLocalizedModule.smul_injective (f := LocalizedModule.mkLinearMap S M) ⟨r, hrS⟩)
    simpa using hrxS
  have hpTop : p = ⊤ := by
    apply top_unique
    intro a ha
    rw [hx]
    simp [Submodule.mem_colon_singleton, hx0]
  exact hpPrime.ne_top hpTop

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
  let fQ : (M ⧸ K) →ₗ[R] LocalizedModule S M :=
    K.liftQ (LocalizedModule.mkLinearMap S M) (by simp [K])
  have hfQ : Function.Injective fQ := by
    apply LinearMap.ker_eq_bot.mp
    simpa [fQ, K] using
      (Submodule.ker_liftQ_eq_bot' K (LocalizedModule.mkLinearMap S M) (by simp [K]))
  intro p hp
  have hpLoc := associatedPrimes.subset_of_injective (R := R) (f := fQ) hfQ hp
  exact associatedPrimes_localizedModule_subset_disjoint (S := S) hpLoc

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
  haveI : p.IsPrime := hp.1
  let K : Submodule R M := LinearMap.ker (LocalizedModule.mkLinearMap S M)
  have hKloc : K.localized (p := p.primeCompl) = ⊥ := by
    change Submodule.localized' (Localization p.primeCompl) p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) K = ⊥
    rw [Submodule.localized'_eq_span]
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).1 hx with ⟨s, hsS, hsx⟩
    have hsP : s ∈ p.primeCompl := fun hsp => Set.notMem_empty s (hpDisj ▸ ⟨hsp, hsS⟩)
    have hxPker : x ∈ LinearMap.ker (LocalizedModule.mkLinearMap p.primeCompl M) :=
      (LocalizedModule.mem_ker_mkLinearMap_iff (S := p.primeCompl) (m := x)).2 ⟨s, hsP, hsx⟩
    simpa [LinearMap.mem_ker] using hxPker
  let eQ := (localizedQuotientEquiv (p := p.primeCompl) (M' := K))
  let eBot := (Submodule.quotEquivOfEqBot (K.localized (p := p.primeCompl)) hKloc)
  let e : LocalizedModule p.primeCompl (M ⧸ K) ≃ₗ[Localization p.primeCompl]
      LocalizedModule p.primeCompl M := eQ.symm.trans eBot
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
      (S := p.primeCompl)
      (R' := Localization.AtPrime p)
      (f := LocalizedModule.mkLinearMap p.primeCompl M)
      (p := IsLocalRing.maximalIdeal (Localization.AtPrime p))
      hAtPrimeM
      ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› _)
  simpa [Localization.AtPrime.comap_maximalIdeal] using hComap


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
    refine ⟨?_, ?_⟩
    · exact (Module.mem_support_iff_of_finite (R := R) (M := M)).2
        (by
          simpa [Submodule.annihilator_top] using
            (IsAssociatedPrime.annihilator_le (M := M) (I := I.asIdeal) hI.1))
    · intro J hJ hJI
      have hAnnJ : Module.annihilator R M ≤ J.asIdeal :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).1 hJ
      obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (J := J.asIdeal) hAnnJ
      have hpAss : p ∈ associatedPrimes R M :=
        Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          (R := R) (M := M) hp
      have hIJ : I.asIdeal ≤ J.asIdeal := (hI.eq_of_ge hpAss <| hpJ.trans hJI) ▸ hpJ
      exact hIJ
  · intro hI
    refine ⟨?_, ?_⟩
    · have hAnnI : Module.annihilator R M ≤ I.asIdeal :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).1 hI.1
      obtain ⟨p, hp, hpI⟩ := Ideal.exists_minimalPrimes_le (J := I.asIdeal) hAnnI
      have hpSupp : (⟨p, hp.1.1⟩ : PrimeSpectrum R) ∈ Module.support R M :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).2 hp.1.2
      have hpEqI : p = I.asIdeal := by
        simpa using (congrArg PrimeSpectrum.asIdeal <| hI.eq_of_ge hpSupp hpI).symm
      exact hpEqI ▸
        Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
          (R := R) (M := M) hp
    · intro J hJ hJI
      have hJSupp : (⟨J, hJ.1⟩ : PrimeSpectrum R) ∈ Module.support R M :=
        (Module.mem_support_iff_of_finite (R := R) (M := M)).2
          (by
            simpa [Submodule.annihilator_top] using
              (IsAssociatedPrime.annihilator_le (M := M) (I := J) hJ))
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
    have hNoDisjAssN : ∀ p ∈ associatedPrimes R N, p.carrier ∩ S ≠ ∅ := by
      intro p hpN hpDisj
      have hpDiff : p ∈ (associatedPrimes R M) \
          { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
        simpa [hAss.1] using hpN
      exact hpDiff.2 ⟨hpDiff.1, hpDisj⟩
    have hLocAssEmpty :
        associatedPrimes (Localization S) (LocalizedModule S N) = ∅ := by
      refine Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro q hq
      have hpre :=
        associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
        (S := S) (R' := Localization S)
        (f := LocalizedModule.mkLinearMap S N)
      have hqComap :
          Ideal.comap (algebraMap R (Localization S)) q ∈ associatedPrimes R N := by
        have : q ∈ (Ideal.comap (algebraMap R (Localization S))) ⁻¹' (associatedPrimes R N) := by
          rw [hpre]
          exact hq
        exact this
      have hqDisjSet :
          Disjoint (S : Set R) ((Ideal.comap (algebraMap R (Localization S)) q : Ideal R) : Set R)
          :=
        (IsLocalization.disjoint_comap_iff S (Localization S) q).mpr hq.1.ne_top
      have hqDisj : (Ideal.comap (algebraMap R (Localization S)) q).carrier ∩ S = ∅ :=
        by simpa [Set.inter_comm] using Set.disjoint_iff_inter_eq_empty.mp hqDisjSet
      exact False.elim ((hNoDisjAssN _ hqComap) hqDisj)
    have hSubLocN : Subsingleton (LocalizedModule S N) := by
      by_contra hns
      haveI : Nontrivial (LocalizedModule S N) := not_subsingleton_iff_nontrivial.mp hns
      obtain ⟨q, hq⟩ := associatedPrimes.nonempty (Localization S) (LocalizedModule S N)
      exact Set.notMem_empty q (hLocAssEmpty ▸ hq)
    have hNleK : N ≤ K := by
      intro x hxN
      have hx0N : LocalizedModule.mkLinearMap S N ⟨x, hxN⟩ = 0 :=
        @Subsingleton.elim (LocalizedModule S N) hSubLocN _ _
      have hxKerN : ⟨x, hxN⟩ ∈ LinearMap.ker (LocalizedModule.mkLinearMap S N) := by
        simpa [LinearMap.mem_ker] using hx0N
      rcases (LocalizedModule.mem_ker_mkLinearMap_iff
          (S := S) (m := (⟨x, hxN⟩ : N))).1 hxKerN with ⟨s, hsS, hsxN⟩
      have hxKerM : x ∈ LinearMap.ker (LocalizedModule.mkLinearMap S M) :=
        (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).2
        ⟨s, hsS, congrArg Subtype.val hsxN⟩
      simpa [K] using hxKerM
    have hKleN : K ≤ N := by
      intro x hxK
      by_contra hxN
      let xq : M ⧸ N := N.mkQ x
      have hxq_ne : xq ≠ 0 := by simpa [xq, Submodule.Quotient.mk_eq_zero] using hxN
      let C : Submodule R (M ⧸ N) := Submodule.span R ({xq} : Set (M ⧸ N))
      have hxq_mem_C : xq ∈ C := Submodule.subset_span (by simp [xq])
      have hxq_sub_ne : (⟨xq, hxq_mem_C⟩ : C) ≠ 0 := by
        intro h
        apply hxq_ne <| Subtype.ext_iff.mp h
      have hxq_sub_ne' : (0 : C) ≠ ⟨xq, hxq_mem_C⟩ := by
        simpa [eq_comm] using hxq_sub_ne
      haveI : Nontrivial C := ⟨⟨0, by simp [C]⟩, ⟨⟨xq, hxq_mem_C⟩, by
        exact hxq_sub_ne'⟩⟩
      obtain ⟨p, hpC⟩ := associatedPrimes.nonempty R C
      have hpMN : p ∈ associatedPrimes R (M ⧸ N) :=
        associatedPrimes.subset_of_injective (R := R) (f := C.subtype)
          (Submodule.injective_subtype C) hpC
      have hpDisj : p.carrier ∩ S = ∅ := by
        have hpSet : p ∈ { p ∈ associatedPrimes R M | p.carrier ∩ S = ∅ } := by
          simpa [hAss.2] using hpMN
        exact hpSet.2
      rcases hpC with ⟨hpPrime, y, hy⟩
      rcases (LocalizedModule.mem_ker_mkLinearMap_iff (S := S) (m := x)).1 (by simpa [K] using hxK)
        with ⟨s, hsS, hsx⟩
      have hsxq : s • xq = 0 := by
        change N.mkQ (s • x) = 0
        simp [hsx]
      have hsy : s • y = 0 := by
        apply Subtype.ext
        change s • (y : M ⧸ N) = 0
        rcases Submodule.mem_span_singleton.mp y.2 with ⟨r, hr⟩
        have hr' : (y : M ⧸ N) = r • xq := by
          simpa [eq_comm] using hr
        rw [hr']
        calc
          s • (r • xq) = (s * r) • xq := by simp [smul_smul]
          _ = r • (s • xq) := by simp [smul_smul, mul_comm]
          _ = 0 := by simp [hsxq]
      have hsP : s ∈ p := by
        rw [hy]
        simpa [Submodule.mem_colon_singleton] using hsy
      exact Set.notMem_empty s (hpDisj ▸ ⟨hsP, hsS⟩)
    simpa [K] using le_antisymm hNleK hKleN
  · intro hN
    subst hN
    refine ⟨associatedPrimes_ker_mkLinearMap_eq (S := S), ?_⟩
    refine le_antisymm ?_ (disjoint_associatedPrimes_subset_associatedPrimes_quot_ker_mkLinearMap
      (S := S))
    intro p hp
    refine ⟨?_, associatedPrimes_quot_ker_mkLinearMap_subset_disjoint (S := S) hp⟩
    exact mem_associatedPrimes_of_mem_associatedPrimes_quot_ker_mkLinearMap_of_disjoint
      (S := S) hp <| associatedPrimes_quot_ker_mkLinearMap_subset_disjoint (S := S) hp

end CommutativeAlgebra
end HarderNarasimhan
