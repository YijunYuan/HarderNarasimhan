/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Module.Torsion.Basic

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Semistability.Translation
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.CoprimaryFiltration.CommutativeAlgebra

import HarderNarasimhan.CoprimaryFiltration.Defs

/-!
Implementation for coprimary filtrations.

This file develops the commutative-algebraic input needed to apply the general
Harder–Narasimhan filtration theory to the slope `μ R M` built from associated
primes.

High-level structure:

* Show `_μ R M I` is nonempty and behaves monotonically under enlarging the right
  endpoint of an interval.
* Derive basic slope properties (`μmax_eq_μ`) and prove convexity of `μ R M`.
* Compute `μA (μ R M) I` explicitly as the singleton containing the minimal
  associated prime of the relevant quotient.
* Prove well-foundedness of the submodule lattice and a descending chain condition
  for `μA`, enabling the general HN filtration construction.
* Relate semistability of restricted slopes to semistability on quotient modules,
  and use this to build coprimary filtrations.

Some classical results are still assumed via `HarderNarasimhan.CommutativeAlgebra`.

API note: most downstream files should import `HarderNarasimhan.CoprimaryFiltration.Results`
instead of this implementation file. This module is large and contains commutative-algebraic
infrastructure.
-/

namespace HarderNarasimhan

namespace impl

/--
Nonemptiness of the finset of associated primes for any strict interval.

For a strict inclusion `N₁ < N₂`, the quotient `N₂ / N₁` is nontrivial, hence it has
at least one associated prime; this yields a nonempty finset `_μ R M I`.
-/
lemma μ_nonempty {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty := by
  intro I
  simp only [Set.toFinset_nonempty]
  have : Nontrivial (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2) := by
    rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
    exact fun h => not_lt_of_ge h I.prop
  rcases associatedPrimes.nonempty R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_ofPred.mpr ?_⟩
  use q, hq

/--
Monotonicity of `associatedPrimes` along the canonical map `A/N ↪ B/N` when `A ≤ B`.

If `N, A, B` are submodules with `A ≤ B`, the inclusion `A ↪ B` induces an injection
`A / N.submoduleOf A → B / N.submoduleOf B`, and pushing associated primes along this
injection yields the displayed inclusion.
-/
lemma associatedPrimes_subset_of_submoduleOf_le
{R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(N A B : Submodule R M) (h : A ≤ B) :
associatedPrimes R (↥A ⧸ N.submoduleOf A) ⊆ associatedPrimes R (↥B ⧸ N.submoduleOf B) := by
  have hcomap : Submodule.comap (Submodule.inclusion h) (N.submoduleOf B) = N.submoduleOf A := rfl
  refine associatedPrimes.subset_of_injective
    (f := (N.submoduleOf A).mapQ (N.submoduleOf B) (Submodule.inclusion h) (le_of_eq hcomap.symm))
    ?_
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]

/-- Monotonicity of `_μ` in the right endpoint.

  If `N₁ < u ≤ N₃`, then every associated prime of `u / N₁` is also an associated
  prime of `N₃ / N₁` (after translating into the `LinearExtension` wrapper). This is
  the key subset relation used to show monotonicity of the slope value.
-/
lemma _μ_mono_right {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ u N₃ : Submodule R M}
(h₁ : N₁ < u) (h₂ : u ≤ N₃)
:
_μ R M ⟨(N₁, u), h₁⟩ ⊆ _μ R M ⟨(N₁, N₃), lt_of_lt_of_le h₁ h₂⟩ := by
  rintro i ⟨p, hp1, hp2⟩
  exact ⟨p, associatedPrimes_subset_of_submoduleOf_le N₁ u N₃ h₂ hp1, hp2⟩


/--
For the associated-prime slope, `μmax` is definitionally redundant.

The definition of `μ R M` already yields an element that is greatest among the
subinterval values, so the `μmax` operation returns the same value.
-/
lemma μmax_eq_μ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := by
  intro I
  unfold μmax
  apply IsGreatest.csSup_eq
  unfold IsGreatest
  constructor
  · simp only [ne_eq, Set.mem_ofPred_eq]
    use I.val.2
    use ⟨⟨le_of_lt I.prop,le_rfl⟩,ne_of_lt I.prop⟩
  · apply mem_upperBounds.2
    intro x hx
    simp only [ne_eq, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨u,⟨hu1,hu2⟩⟩
    rw [← hu2]
    unfold μ
    rw [DedekindCut.principal_le_principal]
    apply S₀_order.1
    exact Set.toFinset_subset_toFinset.mpr <| _μ_mono_right (lt_of_le_of_ne hu1.1.1 hu1.2) hu1.1.2

/--
Proposition 3.11 (internal form): convexity of `μ R M` on the total interval.

We prove `ConvexI TotIntvl (μ R M)` first, and later export it as global `Convex`.
The key step is that subset inclusion between associated-prime sets implies `≤` in
the chosen `S₀ R` order.
-/
instance prop3d11 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
ConvexI TotIntvl (μ R M) := by
  refine { convex := fun x y _ _ hxy ↦ ?_ }
  unfold μ
  rw [DedekindCut.principal_le_principal]
  refine S₀_order.1 (_μ R M ⟨(x ⊓ y, x), inf_lt_left.mpr hxy⟩).toFinset
    (_μ R M ⟨(y, x ⊔ y), right_lt_sup.mpr hxy⟩).toFinset (Set.toFinset_subset_toFinset.mpr ?_)
  unfold _μ
  intro w hw
  simp only [Set.mem_ofPred_eq] at *
  rcases hw with ⟨p,⟨hp1,hp2⟩⟩
  use p
  simp only [hp2, exists_prop, and_true]
  rw [AssociatedPrimes.mem_iff] at hp1 ⊢
  exact (LinearEquiv.isAssociatedPrime_iff (LinearMap.quotientInfEquivSupQuotient x y)).1 hp1

/--
Membership in module support from an associated prime.

Any associated prime of `M` is, by definition, the annihilator of some element; this
implies the corresponding prime lies in `Module.support R M`.

This is a small bridge lemma used when comparing minimality in `associatedPrimes`
versus minimality in `support`.
-/
lemma mem_support_of_mem_associatedPrimes {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M] {x : Ideal R} :
(hx : x ∈ associatedPrimes R M) →  {asIdeal := x, isPrime := hx.out.1} ∈  Module.support R M := by
  intro hx
  apply Module.mem_support_iff_exists_annihilator.2
  have hx' : IsAssociatedPrime x M := (AssociatedPrimes.mem_iff (R := R) (M := M)).1 hx
  rcases hx' with ⟨_, m, hpm⟩
  use m
  change (R ∙ m).annihilator ≤ x
  rw [hpm]
  simpa [Submodule.bot_colon'] using (Ideal.le_radical : (⊥ : Submodule R M).colon {m} ≤ _)

/--
Monotonicity of support under enlarging the submodule being quotiented out.

If `N₁ ≤ N₂`, then the support of `N₃ / N₂` is contained in the support of
`N₃ / N₁`. This is a standard “support shrinks under quotients” statement.
-/
lemma support_quotient_mono {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(N₁ N₂ N₃ : Submodule R M) (h : N₁ ≤ N₂) :
  Module.support R (N₃⧸ N₂.submoduleOf N₃) ⊆ Module.support R (N₃⧸ N₁.submoduleOf N₃) :=
  Module.support_subset_of_surjective (Submodule.factor (Submodule.comap_mono h))
    (Submodule.factor_surjective _)

/--
Existence of a minimal prime in the support below a given supported prime.

For a finite module over a Noetherian ring, any prime in the support is above a
minimal element of the support.

This is used to compare arbitrary associated primes to the minimum element selected
by `Finset.min'`.
-/
lemma exists_minimal_prime_contained_supp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ q : PrimeSpectrum R, q ∈ Module.support R M →
  ∃ p : PrimeSpectrum R, Minimal (fun J ↦ J ∈ Module.support R M) p ∧ p ≤ q := by
  intro q hq
  rcases Ideal.exists_minimalPrimes_le <| Module.mem_support_iff_of_finite.1 hq with ⟨r,hr⟩
  use ⟨r, hr.1.out.1.1⟩
  refine ⟨?_,hr.2⟩
  simp only [Module.mem_support_iff_of_finite]
  exact ⟨hr.1.out.1.2, fun y hy1 hy2 ↦ hr.1.out.2 ⟨y.isPrime,hy1⟩ hy2⟩

/--
Lower bound property of the minimal associated prime.

Given an intermediate submodule `N''` in an interval `I`, any associated prime of
`I.val.2 / N''` is ≥ the minimal element of `_μ R M I`.

This uses the admitted equivalence between minimal associated primes and minimal
support, plus the existence of minimal primes in the support.
-/
lemma prop3d12p1 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
(N'' : ℒ R M) (ha1 : InIntvl I N'') :
∀ q : Ideal R, (hq : q ∈ associatedPrimes R (I.val.2⧸N''.submoduleOf I.val.2)) →
  {asIdeal := q, isPrime := hq.out.1 } ≥ (((_μ R M) I).toFinset.min' (μ_nonempty I)) := by
  intro q hq
  have hq' := support_quotient_mono I.val.1 N'' I.val.2 (ha1.1) <|
    mem_support_of_mem_associatedPrimes hq
  obtain ⟨r,hr,hr'⟩ := exists_minimal_prime_contained_supp {asIdeal := q, isPrime := hq.out.1 } hq'
  rw [← CommutativeAlgebra.min_associated_prime_iff_min_supp] at hr
  refine le_trans ?_ <| toLinearExtension.monotone' hr'
  refine (((_μ R M) I).toFinset.min'_le) (toLinearExtension r) ?_
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨r.asIdeal, hr.1, rfl⟩


/--
Singleton lower bound for `μA`: the chosen minimal prime is ≤ every tail `_μ`.

Specializing the previous lemma to the minimal element of a smaller interval, we
obtain the order relation needed to show that the singleton `{min}` is the infimum
in the definition of `μA`.
-/
lemma prop3d12p2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
(N'' : ℒ R M) (ha1 : InIntvl I N'') (ha2 : N'' ≠ I.val.2) :
@LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I}
  (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset := by
  have : @LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I}
    {(_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty _} := by
    rw [← S₀_order.2]
    have this' : ((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <|
      μ_nonempty _).asIdeal ∈ associatedPrimes R (↥I.val.2 ⧸ Submodule.submoduleOf N'' I.val.2):= by
      have := ((_μ R M ⟨(N'', I.val.2),
        lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty _).out
      simp only [Finset.mem_val, Set.mem_toFinset, Set.mem_ofPred_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rwa [← hp2]
    exact prop3d12p1 I N'' ha1 (((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'
      <| μ_nonempty _).asIdeal) this'
  refine le_trans this ?_
  apply S₀_order.1
  simp only [Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
  exact Set.mem_toFinset.mp <|
    (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty _

/--
Auxiliary localization map used in the `μA` computation.

`CP.f1 I` is the canonical map into the localization of the quotient module
`I.val.2 / I.val.1`, localized away from the (chosen) minimal associated prime.
-/
noncomputable abbrev CP.f1 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :=
  LocalizedModule.mkLinearMap (
    ((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl
    (I.val.2⧸I.val.1.submoduleOf I.val.2)

/-- Quotient map used in the `μA` computation.

  `CP.f2 I` is the linear map `I.val.2 → I.val.2 / I.val.1`.
-/
abbrev CP.f2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
I.val.2 →ₗ[R] (I.val.2⧸I.val.1.submoduleOf I.val.2) :=
  (I.val.1.submoduleOf I.val.2).mkQ

/--
Kernel lifted back to a submodule of `M`.

We consider the kernel of the composition `CP.f1 I ∘ CP.f2 I` on `I.val.2` and map it
back into `M`. This submodule serves as the intermediate `N''` that realizes the
infimum in the definition of `μA`.
-/
noncomputable abbrev ker_of_quot_comp_localization {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
: ℒ R M :=
Submodule.map I.val.2.subtype (LinearMap.ker ((CP.f1 I) ∘ₗ (CP.f2 I)))

/--
Mapping a submodule of `N` to a submodule of `M` and restricting back.

This is a small bookkeeping lemma about `Submodule.map`/`submoduleOf` used to simplify
some of the quotient arguments below.
-/
lemma submoduleOf_map_subtype {R : Type*} [CommRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M]
(N : Submodule R M) (N' : Submodule R ↥N) : N' = (Submodule.map (N.subtype) N').submoduleOf N :=
  (Submodule.comap_map_eq_of_injective N.subtype_injective N').symm

/-- An isomorphism rewriting a quotient by `ker_of_quot_comp_localization`.

  This lemma constructs a `LinearEquiv` identifying

  `I.val.2 / ker_of_quot_comp_localization I`

  with a quotient of `I.val.2 / I.val.1` by the kernel of the localization map
  `CP.f1 I`.

  It is a technical step toward computing the associated primes of the intermediate
  quotient used in the proof of `prop3d12`.
-/
lemma koqcl_iso {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
∃ _ : LinearEquiv (RingHom.id R) (I.val.2⧸((ker_of_quot_comp_localization I).submoduleOf I.val.2))
  ((I.val.2⧸(I.val.1.submoduleOf I.val.2))⧸ (LinearMap.ker (CP.f1 I))), True := by
  unfold ker_of_quot_comp_localization
  let S : Submodule R I.val.2 := I.val.1.submoduleOf I.val.2
  let T : Submodule R I.val.2 := LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I)
  have hT_eq : T = Submodule.comap S.mkQ (LinearMap.ker (CP.f1 I)) := by
    change LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I) = _
    rw [LinearMap.ker_comp]
  have hST : S ≤ T := hT_eq ▸ Submodule.le_comap_mkQ _ _
  have hsubT : T = (Submodule.map I.val.2.subtype T).submoduleOf I.val.2 :=
    submoduleOf_map_subtype I.val.2 T
  have hST' : S ≤ (Submodule.map I.val.2.subtype T).submoduleOf I.val.2 := hsubT ▸ hST
  have hmap : Submodule.map S.mkQ ((Submodule.map I.val.2.subtype T).submoduleOf I.val.2) =
      LinearMap.ker (CP.f1 I) := by
    rw [← hsubT, hT_eq, Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)]
  exact ⟨hmap ▸ (Submodule.quotientQuotientEquivQuotient S _ hST').symm, trivial⟩

/--
Associated primes of the intermediate quotient are a singleton.

After localizing away from the minimal associated prime, the admitted Bourbaki-style
statement implies that the only associated prime that remains is exactly that
minimal one. This yields the singleton formula used in `prop3d12`.
-/
lemma associated_primes_quot_koqcl {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
associatedPrimes R (I.val.2⧸(ker_of_quot_comp_localization I).submoduleOf I.val.2) =
  {(((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal}
:= by
  rcases koqcl_iso I with ⟨h, _⟩
  rw [LinearEquiv.AssociatedPrimes.eq h]
  have := CommutativeAlgebra.bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6
    ((((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl) (LinearMap.ker (CP.f1 I))
  simp only [iff_true] at this
  rw [this.2]
  ext q
  constructor
  · intro hq
    simp only [Set.mem_ofPred_eq] at hq
    simp only [Set.mem_singleton_iff]
    replace := ((_μ R M) I).toFinset.min'_le (toLinearExtension ⟨q, hq.1.out.1⟩)
      (Set.mem_toFinset.mpr ⟨q, hq.1, rfl⟩)
    have hle : (⟨q, hq.1.out.1⟩ : PrimeSpectrum R) ≤ (_μ R M I).toFinset.min' (μ_nonempty I) :=
      Set.sdiff_eq_empty.mp hq.2
    have heq : toLinearExtension ⟨q, hq.1.out.1⟩ = (_μ R M I).toFinset.min' (μ_nonempty I) :=
      eq_of_le_of_ge (toLinearExtension.monotone' hle) this
    exact congrArg PrimeSpectrum.asIdeal heq
  · intro hq
    simp only [Set.sdiff_sep_self, Set.mem_singleton_iff,
      Set.mem_ofPred_eq] at *
    rw [hq]
    constructor
    · replace := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
      simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at this
      rcases this with ⟨_,⟨hp1,hp2⟩⟩
      exact hp2 ▸ hp1
    · unfold Ideal.primeCompl
      simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.inter_compl_self]

/--
Proposition 3.12 (internal): explicit computation of `μA (μ R M)`.

For any strict interval `I : N₁ < N₂`, the auxiliary function `μA` evaluates to the
singleton finset containing the minimal element of `_μ R M I` (in the `S₀ R` order).

Proof idea:

* Show that the intermediate submodule `ker_of_quot_comp_localization I` realizes an
  element of the defining set for the `inf` in `μA`.
* Use `prop3d12p2` to show it is a lower bound, hence an infimum.
-/
lemma prop3d12 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I =
  ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R) := by
  intro I
  unfold μA
  simp only [μmax_eq_μ, ne_eq]
  unfold μ
  have res1 : (DedekindCut.principal {(_μ R M I).toFinset.min' (μ_nonempty I)} : S R) ∈
    {x | ∃ a, ∃ (h : InIntvl I a ∧ ¬a = I.val.2), DedekindCut.principal
    (_μ R M ⟨(a, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩).toFinset = x} := by
    simp only [Set.mem_ofPred_eq, DedekindCut.principal_inj]
    use ker_of_quot_comp_localization I
    constructor
    · refine (Set.toFinset_congr ?_).trans (Set.toFinset_singleton _)
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact PrimeSpectrum.ext (Set.mem_singleton_iff.mp (associated_primes_quot_koqcl I ▸ hp))
      · rintro rfl
        exact ⟨((_μ R M I).toFinset.min' (μ_nonempty I)).asIdeal,
          by rw [associated_primes_quot_koqcl I]; exact rfl, rfl⟩
    · constructor
      · constructor
        · unfold ker_of_quot_comp_localization
          intro z hz
          simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp,
            Function.comp_apply, Submodule.subtype_apply, Subtype.exists,
            exists_and_right, exists_eq_right]
          use (le_of_lt I.prop) hz
          have : Submodule.Quotient.mk ⟨z, (Iff.of_eq (Eq.refl (z ∈ I.val.2))).mpr
            (le_of_lt (Subtype.prop I) hz) ⟩ =
            (0 : ↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2)
            := by simpa only [Submodule.Quotient.mk_eq_zero]
          exact (congrArg (LocalizedModule.mk · 1) this).trans (LocalizedModule.zero_mk 1)
        · unfold ker_of_quot_comp_localization
          simp only [Submodule.map_subtype_le]
      · by_contra hc
        have := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
        simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at this
        rcases this with ⟨p,⟨hp1,hp2⟩⟩
        apply mem_support_of_mem_associatedPrimes at hp1
        replace hp1 := hp1.out
        have : LinearMap.ker (CP.f1 I) ≠ ⊤ := by
          by_contra hc
          apply LocalizedModule.subsingleton_iff_ker_eq_top.2 at hc
          rw [hp2] at hp1
          exact false_of_nontrivial_of_subsingleton (LocalizedModule
            ((_μ R M I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl
            (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2))
        have : ∃ m : (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2), (CP.f1 I) m ≠ 0 := by
          by_contra hc
          push Not at hc
          have this' : LinearMap.ker (CP.f1 I) = ⊤ := Submodule.ext fun z ↦
            { mp := fun hz ↦ True.intro, mpr := fun hz ↦ hc z }
          exact this this'
        rcases this with ⟨m,hm⟩
        unfold ker_of_quot_comp_localization at hc
        have this' : (CP.f1 I ∘ₗ CP.f2 I) m.out = 0 := by
          have : m.out.val ∈ Submodule.map (Submodule.subtype I.val.2)
            (LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I)) := by
            have := m.out.prop
            conv at this =>
              arg 1; simp only [← hc]
            exact this
          simp only [ne_eq, LinearMap.ker_eq_top, LocalizedModule.mkLinearMap_apply,
            Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp,
            Function.comp_apply, Submodule.subtype_apply,
            SetLike.coe_eq_coe, exists_eq_right] at *
          exact this
        unfold CP.f2 at this'
        simp only [Submodule.mkQ_apply, LinearMap.coe_comp, Function.comp_apply] at this'
        unfold Submodule.Quotient.mk Quotient.mk'' at this'
        rw [Quotient.out_eq] at this'
        exact hm this'
  apply IsLeast.csInf_eq
  refine ⟨res1,?_⟩
  apply mem_lowerBounds.2
  rintro N ⟨a,ha1,ha2⟩
  rw [← ha2]
  rw [DedekindCut.principal_le_principal]
  exact prop3d12p2 I a ha1.1 ha1.2

/--
Proposition 3.13 (part 1): the strict order on `ℒ R M` is well-founded.

This is mathlib's `wellFoundedGT` instance for submodule lattices of Noetherian modules;
we only record the correspondence to the paper's numbering here.
-/
lemma prop3d13₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
WellFoundedGT (ℒ R M) := wellFoundedGT

/--
Proposition 3.13 (part 2): the associated-prime slope satisfies the `μA` descending
chain condition.

Concretely, any strict chain of submodules would produce infinitely many distinct
associated primes of a fixed finitely generated module, contradicting finiteness of
`associatedPrimes` over a Noetherian ring.
-/
instance prop3d13₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
μA_DescendingChainCondition (μ R M) where
  μ_dcc := by
    intro N x hx1 hx2
    by_contra hc
    simp only [not_exists] at hc
    simp only [prop3d12] at hc
    simp only [DedekindCut.principal_lt_principal, not_lt, not_le] at hc
    have hc := fun w ↦ S₀_order'.mpr (by
      simpa only [DedekindCut.principal_lt_principal] using (hc w)
      )
    have s1 : ∀ i, ((_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min' <| μ_nonempty _).asIdeal ∈
      associatedPrimes R ((x i)⧸(Submodule.submoduleOf N (x i))) := by
      intro i
      have := (_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min'_mem (μ_nonempty _)
      simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at this
      rcases this with ⟨_,⟨_,hp2⟩⟩
      rwa [← hp2]
    have s2 : ∀ i,
      associatedPrimes R (↥(x i) ⧸ Submodule.submoduleOf N (x i)) ⊆
      associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0)) := by
      intro i
      refine associatedPrimes_subset_of_submoduleOf_le N (x i) (x 0) ?_
      if hi : i = 0 then
        rw [hi]
      else
        exact le_of_lt (hx2 (Nat.zero_lt_of_ne_zero hi))
    have : (associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0))).Infinite := by
      refine Set.infinite_of_injective_forall_mem ?_ <| fun i ↦ s2 i (s1 i)
      intro a b hab
      by_contra!
      have help : ∀ A B : LinearExtension (PrimeSpectrum R), A.asIdeal = B.asIdeal → A = B :=
            fun _ _ h ↦ PrimeSpectrum.ext h
      rcases ne_iff_lt_or_gt.1 this with this | this
      · have := strictMono_nat_of_lt_succ hc this
        rw [help ((_μ R M ⟨(N, x a), hx1 a⟩).toFinset.min' (μ_nonempty _))
          ((_μ R M ⟨(N, x b), hx1 b⟩).toFinset.min' (μ_nonempty _)) hab] at this
        exact (lt_self_iff_false _).1 this
      · have := strictMono_nat_of_lt_succ hc this
        rw [help ((_μ R M ⟨(N, x a), hx1 a⟩).toFinset.min' (μ_nonempty _))
          ((_μ R M ⟨(N, x b), hx1 b⟩).toFinset.min' (μ_nonempty _)) hab] at this
        exact (lt_self_iff_false _).1 this
    exact this <| associatedPrimes.finite R ((↥(x 0) ⧸ Submodule.submoduleOf N (x 0)))

/--
First characterization of semistability for the associated-prime slope.

Semistability of `μ R M` is equivalent to the statement that the `μA` value of every
nontrivial submodule `N` equals the constant singleton corresponding to the minimal
associated prime of `M`.

This is the main algebraic input behind Remark 3.14 in the public results.
-/
lemma rmk4d14₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨(⊥,N),hN⟩ =
  ({(((_μ R M) ⟨(⊥,⊤),bot_lt_top⟩).toFinset.min' (μ_nonempty _))} : S₀ R) := by
  constructor
  · intro hst N hN
    replace hst := hst.semistable N (bot_lt_iff_ne_bot.1 hN)
    rw [prop3d12 ⟨(⊥,N),hN⟩, prop3d12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩] at hst
    rw [prop3d12 ⟨(⊥,N),hN⟩]
    simp only [DedekindCut.principal_inj, Finset.singleton_inj]
    simp only [gt_iff_lt, DedekindCut.principal_lt_principal, not_lt] at hst
    apply (S₀_order.2 _ _).2 at hst
    exact eq_of_le_of_ge hst <| Finset.min'_subset (μ_nonempty _) <|
      Set.toFinset_subset_toFinset.mpr <| _μ_mono_right hN fun ⦃x⦄ a ↦ by trivial
  · intro h
    refine { semistable := ?_ }
    intro N hN
    specialize h N (bot_lt_iff_ne_bot.2 hN)
    have t1 := prop3d12 ⟨(⊥,N),bot_lt_iff_ne_bot.2 hN⟩
    have t2 := prop3d12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩
    rw [prop3d12 ⟨(⊥,N),bot_lt_iff_ne_bot.2 hN⟩] at h
    simp only [DedekindCut.principal_inj, Finset.singleton_inj] at h
    rw [t1,t2]
    simp only [gt_iff_lt, DedekindCut.principal_lt_principal, not_lt, ge_iff_le]
    apply (S₀_order.2 _ _).1
    rw [h]

/-- Second characterization of semistability: semistable iff unique associated prime.

  Combining `rmk4d14₁` with the explicit formula for `μA`, we show that `Semistable (μ R M)`
  is equivalent to the classical condition `∃! p, p ∈ associatedPrimes R M`.
-/
lemma rmk4d14₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [rmk4d14₁]
  let p0 := ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min' (μ_nonempty _))
  have hbot (N : ℒ R M) : Submodule.submoduleOf (⊥ : ℒ R M) N = ⊥ :=
    Submodule.ker_subtype N
  let eTop :
      (↥(⊤ : ℒ R M) ⧸ Submodule.submoduleOf (⊥ : ℒ R M) ⊤) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ (hbot ⊤)).trans Submodule.topEquiv
  have hp0 : p0.asIdeal ∈ associatedPrimes R M := by
    have hp := ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_mem (μ_nonempty _))
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hp
    rcases hp with ⟨q, hq, hq'⟩
    have hqM : q ∈ associatedPrimes R M := by
      simpa [LinearEquiv.AssociatedPrimes.eq eTop] using hq
    have hp0_eq : p0.asIdeal = q := by
      rw [show p0 = { asIdeal := q, isPrime := hq.out.1 } by simpa [p0] using hq'.symm]
    rwa [hp0_eq]
  have h_ext : ∀ A B : LinearExtension (PrimeSpectrum R), A.asIdeal = B.asIdeal → A = B :=
    fun _ _ h ↦ PrimeSpectrum.ext h
  constructor
  · refine fun hs => ⟨p0.asIdeal, hp0, fun J hJ => ?_⟩
    have hJ' : IsAssociatedPrime J M := (AssociatedPrimes.mem_iff (R := R) (M := M)).1 hJ
    rcases (isAssociatedPrime_iff (R := R) (M := M)).1 hJ' with ⟨hJp, t, ht⟩
    let N : ℒ R M := Submodule.span R {t}
    let eN : (↥N ⧸ Submodule.submoduleOf (⊥ : ℒ R M) N) ≃ₗ[R] ↥N :=
      Submodule.quotEquivOfEqBot _ (hbot N)
    have hN : ⊥ < N := by
      refine bot_lt_iff_ne_bot.mpr <| fun ht0 => ?_
      have : t = 0 := Submodule.span_singleton_eq_bot.mp ht0
      exact hJp.ne_top <| by rw [ht, this, Submodule.colon_singleton_zero]
    have hJN : ⟨J, hJp⟩ ∈ _μ R M ⟨(⊥, N), hN⟩ := by
      simp only [_μ]
      refine ⟨J, ?_, rfl⟩
      have hJN' : J ∈ associatedPrimes R ↥N := by
        refine (AssociatedPrimes.mem_iff (R := R) (M := ↥N)).2 ?_
        refine (isAssociatedPrime_iff (R := R) (M := ↥N)).2 ⟨hJp, ⟨⟨t,
          Submodule.mem_span_singleton_self t⟩, ?_⟩⟩
        ext r
        rw [ht]
        simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
        constructor
        · intro hr
          exact Subtype.ext hr
        · intro hr
          exact congrArg Subtype.val hr
      simpa [LinearEquiv.AssociatedPrimes.eq eN] using hJN'
    have hJ_le : ∀ q ∈ _μ R M ⟨(⊥, N), hN⟩, ⟨J, hJp⟩ ≤ q := by
      intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      rcases hq with ⟨I, hI, rfl⟩
      have hI' : I ∈ associatedPrimes R ↥N := by
        simpa [LinearEquiv.AssociatedPrimes.eq eN] using hI
      have hI_supp := mem_support_of_mem_associatedPrimes hI'
      have hAnn : N.annihilator = J := by
        ext r
        rw [show N = Submodule.span R {t} by rfl, ht, Submodule.mem_annihilator_span_singleton,
          Submodule.bot_colon', Submodule.mem_annihilator_span_singleton]
      refine toLinearExtension.monotone' ?_
      have h := (Module.mem_support_iff_of_finite (R := R) (M := ↥N)).1 hI_supp
      change J ≤ I
      rw [← hAnn]
      exact h
    have hmin : ((_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _)) = ⟨J, hJp⟩ := by
      refine le_antisymm ((_μ R M ⟨(⊥, N), hN⟩).toFinset.min'_le _ <| Set.mem_toFinset.mpr hJN) ?_
      exact hJ_le _ <| Set.mem_toFinset.mp <|
        ((_μ R M ⟨(⊥, N), hN⟩).toFinset.min'_mem (μ_nonempty _))
    have hs' := hs N hN
    rw [prop3d12 ⟨(⊥, N), hN⟩] at hs'
    simp only [DedekindCut.principal_inj, Finset.singleton_inj] at hs'
    have hEq : ({ asIdeal := J, isPrime := hJp } : LinearExtension (PrimeSpectrum R)) = p0 :=
      hmin.symm.trans hs'
    rw [← hEq]
  · rintro ⟨p, hp, hp_unique⟩ N hN
    rw [prop3d12 ⟨(⊥, N), hN⟩]
    simp only [DedekindCut.principal_inj, Finset.singleton_inj]
    have hq_top := _μ_mono_right hN le_top <| Set.mem_toFinset.mp <|
        ((_μ R M ⟨(⊥, N), hN⟩).toFinset.min'_mem (μ_nonempty _))
    have hq : (((_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _)).asIdeal) ∈
      associatedPrimes R M := by
      simp only [Set.mem_ofPred_eq] at hq_top
      rcases hq_top with ⟨I, hI, hI'⟩
      have hIM : I ∈ associatedPrimes R M := by
        simpa [LinearEquiv.AssociatedPrimes.eq eTop] using hI
      have hq_eq :
          (((_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _)).asIdeal) = I := by
        rw [show ((_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _)) =
            { asIdeal := I, isPrime := hI.out.1 } by simpa using hI'.symm]
      rwa [hq_eq]
    have hp0_eq : p0.asIdeal = p := hp_unique _ hp0
    have hq_eq :
        (((_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _)).asIdeal) = p := hp_unique _ hq
    exact h_ext _ _ <| by rw [hq_eq, hp0_eq]

/--
Admissibility of the slope `μ R M`.

For the coprimary filtration application we only need the “totality” branch of
`μ_Admissible`: the codomain order is linear, hence total.
-/
instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
μ_Admissible (μ R M) where
  μ_adm := Or.inl inferInstance

open Classical in
/--
Lift a submodule of a quotient back to a submodule of the ambient module.

Given `x ≤ N₂ / N₁`, we define `lift_quot N₁ N₂ x` as the preimage of `x` under the
quotient map `N₂ → N₂ / N₁`, mapped into `M` via the subtype inclusion `N₂ ↪ M`.

This is used to relate semistability of a restricted slope (on an interval) to
semistability of the induced slope on the quotient lattice.
-/
def lift_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : Submodule R M)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) : Submodule R M :=
  Submodule.map N₂.subtype (Submodule.comap (N₁.submoduleOf N₂).mkQ x)

/--
Basic bounds for `lift_quot`.

If `N₁ ≤ N₂`, then `N₁ ≤ lift_quot N₁ N₂ x ≤ N₂` for any submodule `x` of the
quotient `N₂ / N₁`.
-/
lemma lift_quot_middle {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) :
N₁ ≤ lift_quot N₁ N₂ x ∧ lift_quot N₁ N₂ x ≤ N₂ := by
  refine ⟨?_, Submodule.map_subtype_le _ _⟩
  refine le_trans ?_ (Submodule.map_mono (Submodule.le_comap_mkQ _ _))
  change N₁ ≤ Submodule.map N₂.subtype (N₁.submoduleOf N₂)
  rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right.2 hN]

/-- Nontriviality is preserved by `lift_quot`.

  If `x ≠ ⊥` as a submodule of the quotient `N₂ / N₁`, then the lifted submodule
  `lift_quot N₁ N₂ x` is not equal to `N₁`.
-/
lemma lift_quot_not_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) (hx : x ≠ ⊥) : lift_quot N₁ N₂ x ≠ N₁:= by
  intro hc
  refine hx ?_
  have h_comap : Submodule.comap (N₁.submoduleOf N₂).mkQ x = N₁.submoduleOf N₂ := by
    refine le_antisymm ?_ (Submodule.le_comap_mkQ _ _)
    intro a ha
    have ha' : a.val ∈ lift_quot N₁ N₂ x := ⟨a, ha, rfl⟩
    rw [hc] at ha'
    exact ha'
  rw [← (Submodule.comapMkQRelIso (N₁.submoduleOf N₂)).injective.eq_iff]
  exact Subtype.ext (h_comap.trans (Submodule.ker_mkQ _).symm)

/--
Nontriviality of the quotient module for a strict inclusion.

If `N₁ < N₂`, then the quotient `N₂ / N₁` is nontrivial.
-/
lemma quot_ntl {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ : ℒ R M} (hN : N₁ < N₂) : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
  exact fun h => not_lt_of_ge h hN

/--
Nontriviality of the induced submodule lattice on the quotient.

This is the corresponding `Nontrivial` instance for the submodule lattice
`ℒ R (N₂ / N₁)`.
-/
lemma quot_ntl' {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ : ℒ R M} (hN : N₁ < N₂) :
Nontrivial (@ℒ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _)
:= (Submodule.nontrivial_iff R).mpr <| (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)



/-- Quotients on an interval identify with the corresponding quotient submodules. -/
noncomputable def quotEquivMapComap {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ W : ℒ R M} (_ : N₁ ≤ W) (h₂ : W ≤ N₂) :
    (↥W ⧸ N₁.submoduleOf W) ≃ₗ[R]
      Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) := by
  let i : W →ₗ[R] N₂ := Submodule.inclusion h₂
  let f : W →ₗ[R] (↥N₂ ⧸ N₁.submoduleOf N₂) :=
    (N₁.submoduleOf N₂).mkQ.comp i
  have hker : LinearMap.ker f = N₁.submoduleOf W := by
    ext w
    change ((Submodule.Quotient.mk (i w) : ↥N₂ ⧸ N₁.submoduleOf N₂) = 0) ↔ ↑w ∈ N₁
    rw [Submodule.Quotient.mk_eq_zero]
    simp [i, Submodule.submoduleOf]
  have hrange :
      LinearMap.range f =
        Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) := by
    ext x
    constructor
    · rintro ⟨w, -, rfl⟩
      exact Submodule.mem_map_of_mem <| show i w ∈ Submodule.comap N₂.subtype W by
        simp [i]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact
    (Submodule.quotEquivOfEq (N₁.submoduleOf W) (LinearMap.ker f) hker.symm).trans
      ((LinearMap.quotKerEquivRange f).trans (LinearEquiv.ofEq _ _ hrange))

/-- The quotient submodule attached to a nontrivial interval object is nonzero. -/
lemma map_comap_ne_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ W : ℒ R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂) (h₃ : W ≠ N₁) :
    Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) ≠ ⊥ := by
  intro hbot
  refine h₃ <| le_antisymm ?_ h₁
  have hle : Submodule.comap N₂.subtype W ≤ N₁.submoduleOf N₂ := fun y hy => by
    have : y ∈ Submodule.comap (N₁.submoduleOf N₂).mkQ ⊥ := hbot ▸ Submodule.mem_map_of_mem hy
    simpa [Submodule.comap_bot, Submodule.ker_mkQ] using this
  intro x hx
  exact hle (show (⟨x, h₂ hx⟩ : N₂) ∈ Submodule.comap N₂.subtype W from hx)

/-- `_μ` agrees with the quotient version under the submodule correspondence. -/
lemma _mu_eq_quot_mu {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ W : ℒ R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂) (h₃ : W ≠ N₁) :
    _μ R M ⟨(N₁, W), lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
        quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
      letI : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) :=
        quot_ntl' (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
      _μ R (↥N₂ ⧸ N₁.submoduleOf N₂)
        ⟨(⊥,
          Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
    quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
  let : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) :=
    quot_ntl' (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
  let X := Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)
  have hX : Submodule.submoduleOf (⊥ : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)) X = ⊥ :=
    Submodule.ker_subtype X
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro ⟨p, hp, rfl⟩
  · exact ⟨p, by
      rw [LinearEquiv.AssociatedPrimes.eq
        ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
      simpa [X, hX] using hp, rfl⟩
  · exact ⟨p, by
      rw [← LinearEquiv.AssociatedPrimes.eq
        ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
      simpa [X, hX] using hp, rfl⟩

/-- `μA` agrees with the quotient version under the submodule correspondence. -/
lemma muA_eq_quot_muA {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ W : ℒ R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂) (h₃ : W ≠ N₁) :
    μA (μ R M) ⟨(N₁, W), lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
        quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
      letI : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) :=
        quot_ntl' (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
      μA (μ R (↥N₂ ⧸ N₁.submoduleOf N₂))
        ⟨(⊥,
          Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
    quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
  let : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) :=
    quot_ntl' (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
  rw [prop3d12, prop3d12]
  simp only [DedekindCut.principal_inj, Finset.singleton_inj]
  simp [_mu_eq_quot_mu h₁ h₂ h₃]

open Classical in
/--
Semistability of a restriction vs. semistability on the quotient lattice.

This lemma is the key “translation” step for coprimary filtrations:

* restricting the slope `μ R M` to an interval `(N₁, N₂)` corresponds to
* the induced slope on the submodule lattice of the quotient module `N₂ / N₁`.

The statement is phrased as an equivalence between `Semistable (Resμ ...)` and a
`Semistable` predicate on the quotient lattice, with all required `Nontrivial`
instances provided by `quot_ntl`/`quot_ntl'`.
-/
lemma semistable_res_iff_semistable_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N₁ N₂ : ℒ R M) (hN : N₁ < N₂) :
    Semistable (Resμ ⟨(N₁, N₂), hN⟩ (μ R M)) ↔
      @Semistable (@ℒ R _ _ (↥N₂ ⧸ N₁.submoduleOf N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)
        _ _ _) (@quot_ntl' R _ _ M _ _ _ _ N₁ N₂ hN) _ _ (S R) _
        (@μ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)
          (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _) := by
  refine ⟨?_, ?_⟩
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := quot_ntl hN
    let : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) := quot_ntl' hN
    refine { semistable := ?_ }
    intro X hX
    have hres := h.semistable
      ⟨lift_quot N₁ N₂ X, lift_quot_middle N₁ N₂ (le_of_lt hN) X⟩
      (fun hc ↦ lift_quot_not_bot N₁ N₂ X hX (Subtype.coe_inj.mpr hc))
    have hmid := lift_quot_middle N₁ N₂ (le_of_lt hN) X
    have hneq : lift_quot N₁ N₂ X ≠ N₁ := lift_quot_not_bot N₁ N₂ X hX
    have hres' :
        ¬ μA (μ R M) ⟨(N₁, lift_quot N₁ N₂ X), lt_of_le_of_ne hmid.1 hneq.symm⟩ >
          μA (μ R M) ⟨(N₁, N₂), hN⟩ := by
      have := hres
      simp only [μA_res_intvl] at this
      exact this
    rw [muA_eq_quot_muA hmid.1 hmid.2 hneq,
      muA_eq_quot_muA (le_of_lt hN) le_rfl hN.ne.symm] at hres'
    simpa [lift_quot, Submodule.comap_map_eq, Submodule.ker_subtype,
      Submodule.map_comap_eq_self, Submodule.range_mkQ] using hres'
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := quot_ntl hN
    let : Nontrivial (ℒ R (↥N₂ ⧸ N₁.submoduleOf N₂)) := quot_ntl' hN
    refine { semistable := ?_ }
    intro W hW
    have hW' : W.val ≠ N₁ := fun hEq ↦ hW (Subtype.ext hEq)
    have hquot := h.semistable
      (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W.val))
      (map_comap_ne_bot W.prop.1 W.prop.2 hW')
    have hquot' :
        ¬ μA (μ R M) ⟨(N₁, W.val), lt_of_le_of_ne W.prop.1 hW'.symm⟩ >
          μA (μ R M) ⟨(N₁, N₂), hN⟩ := by
      simpa [muA_eq_quot_muA (N₁ := N₁) (N₂ := N₂) (W := W.val)
          W.prop.1 W.prop.2 hW',
        muA_eq_quot_muA (N₁ := N₁) (N₂ := N₂) (W := N₂)
          (le_of_lt hN) le_rfl hN.ne.symm,
        Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ] using hquot
    have hWne : (⊥ : Interval ⟨(N₁, N₂), hN⟩) ≠ W := fun hEq ↦
      hW' (congrArg Subtype.val hEq).symm
    have : ¬ μA (Resμ ⟨(N₁, N₂), hN⟩ (μ R M)) ⟨(⊥, W), lt_of_le_of_ne W.prop.1 hWne⟩ >
        μA (Resμ ⟨(N₁, N₂), hN⟩ (μ R M)) ⟨(⊥, ⊤), bot_lt_top⟩ := by
      simp only [μA_res_intvl]
      exact hquot'
    exact this


open Classical in
/--
Successive quotients in a Harder–Narasimhan filtration are coprimary.

The proof transports semistability of each graded piece to semistability of the
associated-prime slope on that quotient, then applies the characterization of
semistability as having a unique associated prime.
-/
lemma piecewise_coprimary {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(HNFil : HarderNarasimhanFiltration (μ R M)) :
∀ n < Nat.find HNFil.fin_len,
  Coprimary R (↥(HNFil.filtration (n + 1)) ⧸
    Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) := by
  intro n hn
  let hstep := HNFil.strict_mono n (n + 1) (Nat.lt_add_one n) hn
  let := quot_ntl hstep
  let := quot_ntl' hstep
  exact {
    coprimary := rmk4d14₂.mp <|
      (semistable_res_iff_semistable_quot _ _ hstep).mp (HNFil.piecewise_semistable n hn)
  }


/--
Existence of a coprimary filtration.

We build a `CoprimaryFiltration R M` from the canonical Harder–Narasimhan filtration
for the slope `μ R M`, using `piecewise_coprimary` to certify coprimary graded pieces.
-/
noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Inhabited (CoprimaryFiltration R M) := by
  have HNFil := (inferInstance : Inhabited (HarderNarasimhanFiltration (μ R M))).default
  refine { default :=  (
    CoprimaryFiltration.mk HNFil.filtration HNFil.monotone HNFil.first_eq_bot HNFil.fin_len
    HNFil.strict_mono (fun n hn ↦ piecewise_coprimary HNFil n hn) ?_)
  }
  intro n hn
  have := lt_of_not_ge <| HNFil.μA_pseudo_strict_anti n hn
  repeat rw [prop3d12] at this
  simp only [DedekindCut.principal_lt_principal] at this
  apply S₀_order'.2 at this
  have pcn := (piecewise_coprimary HNFil n <| Nat.lt_of_succ_lt hn).coprimary
  have pcnp1 := (piecewise_coprimary HNFil (n+1) hn).coprimary
  have t' : (_μ R M ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)), HNFil.strict_mono
    (n+1) (n+2) (Nat.lt_add_one (n + 1)) hn⟩).toFinset.min' (μ_nonempty _) =
    {asIdeal := pcnp1.exists.choose, isPrime := pcnp1.exists.choose_spec.out.1} := by
    replace := ((_μ R M ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)), HNFil.strict_mono
      (n+1) (n+2) (Nat.lt_add_one (n + 1)) hn⟩).toFinset.min'_mem (μ_nonempty _)).out
    apply Set.mem_toFinset.mp at this
    rcases this.out with ⟨p,hp1,hp2⟩
    rw [← hp2]
    exact PrimeSpectrum.ext (pcnp1.unique pcnp1.exists.choose_spec hp1).symm
  have t'' : (_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1)
    (Nat.lt_add_one n) (Nat.le_of_succ_le hn)⟩).toFinset.min' (μ_nonempty _) =
    {asIdeal := pcn.exists.choose, isPrime := pcn.exists.choose_spec.out.1} := by
    replace := ((_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1)
      (Nat.lt_add_one n) <| le_of_lt hn⟩).toFinset.min'_mem (μ_nonempty _)).out
    apply Set.mem_toFinset.mp at this
    rcases this.out with ⟨p,hp1,hp2⟩
    rw [← hp2]
    exact PrimeSpectrum.ext (pcn.unique pcn.exists.choose_spec hp1).symm
  exact t' ▸ t'' ▸ this

instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Nonempty (CoprimaryFiltration R M) := inferInstance

/--
Any coprimary filtration underlies a Harder–Narasimhan filtration.

We reuse the same filtration function and verify the Harder–Narasimhan axioms:
piecewise semistability (via `rmk4d14₂` and `semistable_res_iff_semistable_quot`) and
strict decrease of the minimal associated primes.
-/
lemma CoprimaryFiltration.toHarderNarasimhanFiltration {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(a : CoprimaryFiltration R M) :
  ∃ HNFil : HarderNarasimhanFiltration (μ R M), a.filtration = HNFil.filtration := by
  let ahn : HarderNarasimhanFiltration (μ R M) := by
      refine HarderNarasimhanFiltration.mk a.filtration a.monotone
        a.first_eq_bot a.fin_len a.strict_mono ?_ ?_
      · intro i hi
        let hstep := a.strict_mono i (i + 1) (Nat.lt_add_one i) hi
        let : Nontrivial (↥(a.filtration (i + 1)) ⧸
            Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1))) := quot_ntl hstep
        let : Nontrivial (ℒ R (↥(a.filtration (i + 1)) ⧸
            Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1)))) := quot_ntl' hstep
        exact (semistable_res_iff_semistable_quot _ _ hstep).mpr <|
          rmk4d14₂.mpr (a.piecewise_coprimary i hi).coprimary
      · intro i hi
        have := a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)
        repeat rw [prop3d12]
        simp only [DedekindCut.principal_le_principal, not_le, gt_iff_lt]
        apply S₀_order'.1
        have e1 : (_μ R M ⟨(a.filtration (i + 1), a.filtration (i + 2)), a.strict_mono (i+1)
            (i+2) (Nat.lt_add_one (i + 1)) hi⟩).toFinset.min' (μ_nonempty _) =
            {asIdeal := (a.piecewise_coprimary (i+1) hi).coprimary.exists.choose,
              isPrime := (a.piecewise_coprimary (i+1) hi).coprimary.exists.choose_spec.out.1} := by
          replace := (_μ R M ⟨(a.filtration (i + 1), a.filtration (i + 2)), a.strict_mono (i+1)
            (i+2) (Nat.lt_add_one (i + 1)) hi⟩).toFinset.min'_mem (μ_nonempty _)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          exact PrimeSpectrum.ext ((a.piecewise_coprimary (i+1) hi).coprimary.unique
            ((a.piecewise_coprimary (i+1) hi).coprimary.exists.choose_spec) hp1).symm
        have e2 : (_μ R M ⟨(a.filtration i, a.filtration (i + 1)), a.strict_mono i
            (i+1) (Nat.lt_add_one i) (Nat.le_of_succ_le hi)⟩).toFinset.min' (μ_nonempty _) =
            {asIdeal := (a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.exists.choose,
              isPrime := (a.piecewise_coprimary i
                (Nat.lt_of_succ_lt hi)).coprimary.exists.choose_spec.out.1} := by
          replace := (_μ R M ⟨(a.filtration i, a.filtration (i + 1)), a.strict_mono i
            (i+1) (Nat.lt_add_one i) (Nat.le_of_succ_le hi)⟩).toFinset.min'_mem (μ_nonempty _)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          exact PrimeSpectrum.ext ((a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.unique
            ((a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.exists.choose_spec)
            hp1).symm
        rw [e1, e2]
        exact a.strict_mono_associated_prime i hi
  use ahn

/--
All coprimary filtrations have the same underlying filtration.

This follows from uniqueness of the Harder–Narasimhan filtration for `μ R M`.
-/
lemma CoprimaryFiltration.filtration_eq_harderNarasimhan_filtration
{R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
  ∀ CPFil : CoprimaryFiltration R M, CPFil.filtration =
    (inferInstance : Inhabited (HarderNarasimhanFiltration (μ R M))).default.filtration := by
  intro CPFil
  rcases (CoprimaryFiltration.toHarderNarasimhanFiltration CPFil) with ⟨HNFil, hfil⟩
  have := @instUniqueHarderNarasimhanFiltration (ℒ R M) _ _ _ _
    (S R) inferInstance (μ R M) (@prop3d13₂ R _ _ M _ _ _ _) _
  rw [hfil,this.uniq HNFil, this.uniq (@default (HarderNarasimhanFiltration (μ R M)) inferInstance)]

/--
Uniqueness of coprimary filtrations.

Since the underlying filtration is uniquely determined, two coprimary filtrations
must coincide.
-/
noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Unique (CoprimaryFiltration R M) where
  uniq := by
    intro a
    have t2 := CoprimaryFiltration.filtration_eq_harderNarasimhan_filtration
      (@default (CoprimaryFiltration R M) inferInstance)
    rw [← CoprimaryFiltration.filtration_eq_harderNarasimhan_filtration a] at t2
    ext
    rw [t2]

end impl

end HarderNarasimhan
