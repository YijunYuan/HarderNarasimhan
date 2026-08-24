/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Algebra.Module.Torsion.Basic

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

The commutative-algebra input (associated primes of the quotient by a localization kernel)
is provided by `HarderNarasimhan.CoprimaryFiltration.CommutativeAlgebra`.

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
∀ I : StrictIntvl (ℒ R M), (_μ R M I).toFinset.Nonempty := by
  intro I
  simp only [Set.toFinset_nonempty]
  have : Nontrivial (↥I.right ⧸ Submodule.submoduleOf I.left I.right) := by
    rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
    exact I.lt.not_ge
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R (I.right⧸(Submodule.submoduleOf I.left I.right))
  exact ⟨⟨q, hq.out.1⟩, hq⟩

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
_μ R M ⟨N₁, u, h₁⟩ ⊆ _μ R M ⟨N₁, N₃, lt_of_lt_of_le h₁ h₂⟩ :=
  fun _ hi ↦ associatedPrimes_subset_of_submoduleOf_le N₁ u N₃ h₂ hi


/--
For the associated-prime slope, `μmax` is definitionally redundant.

The definition of `μ R M` already yields an element that is greatest among the
subinterval values, so the `μmax` operation returns the same value.
-/
lemma μmax_eq_μ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : StrictIntvl (ℒ R M), μmax (μ R M) I = (μ R M) I := by
  intro I
  refine le_antisymm (iSup₂_le fun u hu ↦ ?_) (le_iSup₂_of_le I.right ⟨I.lt, le_rfl⟩ le_rfl)
  exact DedekindCut.principal_le_principal.mpr <| S₀_order.1 _ _ <|
    Set.toFinset_subset_toFinset.mpr <| _μ_mono_right hu.1 hu.2

/--
Proposition 3.11 (internal form): convexity of `μ R M` on the total interval.

We prove `ConvexI ⊤ (μ R M)` first, and later export it as global `Convex`.
The key step is that subset inclusion between associated-prime sets implies `≤` in
the chosen `S₀ R` order.
-/
instance prop3d11 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
ConvexI ⊤ (μ R M) := by
  refine { convex := fun x y _ _ hxy ↦ ?_ }
  refine DedekindCut.principal_le_principal.mpr <| S₀_order.1 _ _ <|
    Set.toFinset_subset_toFinset.mpr ?_
  intro w hw
  rw [Set.mem_ofPred_eq, AssociatedPrimes.mem_iff] at hw ⊢
  exact (LinearEquiv.isAssociatedPrime_iff (LinearMap.quotientInfEquivSupQuotient x y)).1 hw

/--
The chosen minimum of `_μ R M I` is itself an associated prime of the interval quotient.
-/
lemma min'_asIdeal_mem {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M)) :
(((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal ∈
  associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right) :=
  (Set.mem_toFinset (s := _μ R M I)).mp <| ((_μ R M) I).toFinset.min'_mem (μ_nonempty I)

/--
If the interval quotient has a unique associated prime, every associated prime computes the
`Finset.min'` of `_μ R M I`.

This is the bridge between the `Coprimary` predicate on graded pieces and the minimal
associated primes compared by the Harder–Narasimhan axioms.
-/
lemma toLinearExtension_eq_min' {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M))
(hu : ∃! p, p ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right))
{p : PrimeSpectrum R}
(hp : p.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)) :
toLinearExtension p = ((_μ R M) I).toFinset.min' (μ_nonempty I) :=
  PrimeSpectrum.ext (hu.unique hp (min'_asIdeal_mem I))

/--
Lower bound property of the minimal associated prime.

Given an intermediate submodule `N''` in an interval `I`, any associated prime of
`I.right / N''` is ≥ the minimal element of `_μ R M I`.

Mathematically: such a prime `q` contains the annihilator of `I.right / N''`, hence the
annihilator of `I.right / I.left` (of which it is a quotient); a minimal prime over that
annihilator below `q` is an associated prime of `I.right / I.left` (Noetherian, finite),
and the chosen minimum is below it in the linear extension.
-/
lemma prop3d12p1 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M))
(N'' : ℒ R M) (ha1 : N'' ∈ I) :
∀ p : PrimeSpectrum R, p.asIdeal ∈ associatedPrimes R (I.right⧸N''.submoduleOf I.right) →
  (((_μ R M) I).toFinset.min' (μ_nonempty I)) ≤ toLinearExtension p := by
  intro p hp
  have hle : I.left.submoduleOf I.right ≤ N''.submoduleOf I.right :=
    Submodule.comap_mono ha1.1
  have hann : Module.annihilator R (I.right⧸I.left.submoduleOf I.right) ≤ p.asIdeal := by
    rw [← Submodule.annihilator_top]
    refine le_trans ?_ hp.out.annihilator_le
    intro a ha
    rw [Submodule.mem_annihilator] at ha ⊢
    intro x _
    obtain ⟨y, rfl⟩ := Submodule.factor_surjective hle x
    calc a • Submodule.factor hle y
        = Submodule.factor hle (a • y) := (map_smul _ a y).symm
      _ = 0 := by rw [ha y trivial, map_zero]
  obtain ⟨r, hr, hrq⟩ := Ideal.exists_minimalPrimes_le hann
  refine le_trans (((_μ R M) I).toFinset.min'_le (toLinearExtension ⟨r, hr.1.1⟩) <|
    Set.mem_toFinset.mpr <|
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hr) <|
    toLinearExtension.monotone' (hrq : (⟨r, hr.1.1⟩ : PrimeSpectrum R) ≤ p)


/--
Singleton lower bound for `μA`: the chosen minimal prime is ≤ every tail `_μ`.

Specializing the previous lemma to the minimal element of a smaller interval, we
obtain the order relation needed to show that the singleton `{min}` is the infimum
in the definition of `μA`.
-/
lemma prop3d12p2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M))
(N'' : ℒ R M) (ha1 : N'' ∈ I) (ha2 : N'' ≠ I.right) :
@LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I}
  (_μ R M ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset := by
  have h1 : @LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I}
    {(_μ R M ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty _} := by
    rw [← S₀_order.2]
    exact prop3d12p1 I N'' ha1 _ <|
      min'_asIdeal_mem ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩
  exact le_trans h1 <| S₀_order.1 _ _ <| Finset.singleton_subset_iff.mpr <|
    (_μ R M ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty _

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
    rwa [hc] at ha'
  rw [← (Submodule.comapMkQRelIso (N₁.submoduleOf N₂)).injective.eq_iff]
  exact Subtype.ext (h_comap.trans (Submodule.ker_mkQ _).symm)

/--
Third isomorphism theorem for lifted submodules: the quotient of `N₂` by the lift of
`X ≤ N₂ / N₁` is canonically the quotient `(N₂ / N₁) ⧸ X`.
-/
noncomputable def quotLiftQuotEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : ℒ R M)
(X : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)) :
    (↥N₂ ⧸ (lift_quot N₁ N₂ X).submoduleOf N₂) ≃ₗ[R] ((↥N₂ ⧸ N₁.submoduleOf N₂) ⧸ X) :=
  (Submodule.quotEquivOfEq _ _ (Submodule.comap_map_eq_of_injective N₂.subtype_injective _)).trans
    (Submodule.map_comap_eq_self (Submodule.range_mkQ (N₁.submoduleOf N₂) ▸ le_top (a := X)) ▸
      (Submodule.quotientQuotientEquivQuotient (N₁.submoduleOf N₂) _
        (Submodule.le_comap_mkQ _ _)).symm)

/--
The kernel of the localization map of the interval quotient at (the complement of) its
minimal associated prime. Its lift realizes the infimum in the definition of `μA`.
-/
noncomputable abbrev locKer {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M)) :
Submodule R (↥I.right ⧸ I.left.submoduleOf I.right) :=
  LinearMap.ker (LocalizedModule.mkLinearMap
    ((((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl)
    (↥I.right ⧸ I.left.submoduleOf I.right))

/--
Associated primes of the witness quotient form a singleton.

Quotienting by the lifted localization kernel leaves exactly the associated primes disjoint
from the complement of the minimal prime (Bourbaki), i.e. those contained in it; by
minimality of the chosen element in the linear extension, only the minimal prime remains.
-/
lemma associatedPrimes_quot_lift_locKer {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : StrictIntvl (ℒ R M)) :
associatedPrimes R (↥I.right ⧸ (lift_quot I.left I.right (locKer I)).submoduleOf I.right) =
  {(((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal} := by
  rw [LinearEquiv.AssociatedPrimes.eq (quotLiftQuotEquiv I.left I.right (locKer I)),
    CommutativeAlgebra.associatedPrimes_quot_ker_mkLinearMap]
  ext q
  constructor
  · rintro ⟨hq, hdisj⟩
    simp only [Set.mem_singleton_iff]
    have hle : (⟨q, hq.out.1⟩ : PrimeSpectrum R) ≤ (_μ R M I).toFinset.min' (μ_nonempty I) :=
      Set.sdiff_eq_empty.mp hdisj
    have heq : toLinearExtension ⟨q, hq.out.1⟩ = (_μ R M I).toFinset.min' (μ_nonempty I) :=
      eq_of_le_of_ge (toLinearExtension.monotone' hle) <|
        ((_μ R M) I).toFinset.min'_le (toLinearExtension ⟨q, hq.out.1⟩)
          (Set.mem_toFinset.mpr hq)
    exact congrArg PrimeSpectrum.asIdeal heq
  · rintro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    refine ⟨min'_asIdeal_mem I, ?_⟩
    · unfold Ideal.primeCompl
      simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.inter_compl_self]

/--
Proposition 3.12 (internal): explicit computation of `μA (μ R M)`.

For any strict interval `I : N₁ < N₂`, the auxiliary function `μA` evaluates to the
singleton finset containing the minimal element of `_μ R M I` (in the `S₀ R` order).

Proof idea:

* the lift of the localization kernel `locKer I` realizes the value `{min}` by
  `associatedPrimes_quot_lift_locKer` (and is a genuine interior point since the witness
  quotient has an associated prime, hence is nontrivial);
* `prop3d12p2` shows `{min}` is a lower bound.
-/
lemma prop3d12 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : StrictIntvl (ℒ R M), μA (μ R M) I =
  ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R) := by
  intro I
  unfold μA
  simp only [μmax_eq_μ]
  unfold μ
  have hne : lift_quot I.left I.right (locKer I) ≠ I.right := fun hc ↦ by
    have : Subsingleton (↥I.right ⧸ (lift_quot I.left I.right (locKer I)).submoduleOf I.right) :=
      Submodule.Quotient.subsingleton_iff.mpr (Submodule.submoduleOf_eq_top.mpr hc.ge)
    exact Set.singleton_ne_empty _
      ((associatedPrimes_quot_lift_locKer I).symm.trans associatedPrimes.eq_empty_of_subsingleton)
  refine le_antisymm ?_ (le_iInf₂ fun a ha ↦
    DedekindCut.principal_le_principal.mpr <| prop3d12p2 I a ⟨ha.1, ha.2.le⟩ ha.2.ne)
  refine iInf₂_le_of_le (lift_quot I.left I.right (locKer I))
    ⟨(lift_quot_middle I.left I.right I.lt.le (locKer I)).1,
     lt_of_le_of_ne (lift_quot_middle I.left I.right I.lt.le (locKer I)).2 hne⟩ (le_of_eq ?_)
  simp only [DedekindCut.principal_inj]
  refine (Set.toFinset_congr ?_).trans (Set.toFinset_singleton _)
  ext w
  rw [Set.mem_ofPred_eq, associatedPrimes_quot_lift_locKer I, Set.mem_singleton_iff,
    Set.mem_singleton_iff]
  exact ⟨fun h ↦ PrimeSpectrum.ext h, fun h ↦ congrArg PrimeSpectrum.asIdeal h⟩

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
    simp only [not_exists, prop3d12, DedekindCut.principal_lt_principal, not_lt, not_le] at hc
    replace hc := fun w ↦ S₀_order'.mpr (hc w)
    have s1 : ∀ i, ((_μ R M ⟨N, x i, hx1 i⟩).toFinset.min' <| μ_nonempty _).asIdeal ∈
      associatedPrimes R ((x i)⧸(Submodule.submoduleOf N (x i))) :=
      fun i ↦ min'_asIdeal_mem ⟨N, x i, hx1 i⟩
    have s2 : ∀ i,
      associatedPrimes R (↥(x i) ⧸ Submodule.submoduleOf N (x i)) ⊆
      associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0)) :=
      fun i ↦ associatedPrimes_subset_of_submoduleOf_le N (x i) (x 0) (hx2.antitone i.zero_le)
    refine (associatedPrimes.finite R ((↥(x 0) ⧸ Submodule.submoduleOf N (x 0)))).not_infinite ?_
    refine Set.infinite_of_injective_forall_mem ?_ <| fun i ↦ s2 i (s1 i)
    exact fun a b hab ↦ (strictMono_nat_of_lt_succ hc).injective (PrimeSpectrum.ext hab)

/--
First characterization of semistability for the associated-prime slope.

Semistability of `μ R M` is equivalent to the statement that the `μA` value of every
nontrivial submodule `N` equals the constant singleton corresponding to the minimal
associated prime of `M`.

This is the main algebraic input behind Remark 3.14 in the public results.
-/
lemma rmk4d14₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨⊥, N,hN⟩ =
  ({(((_μ R M) ⊤).toFinset.min' (μ_nonempty _))} : S₀ R) := by
  constructor
  · intro hst N hN
    replace hst := hst.semistable N hN
    rw [prop3d12 ⟨⊥, N,hN⟩, prop3d12 (⊤ : StrictIntvl (ℒ R M))] at hst
    rw [prop3d12 ⟨⊥, N,hN⟩]
    simp only [DedekindCut.principal_inj, Finset.singleton_inj]
    simp only [gt_iff_lt, DedekindCut.principal_lt_principal, not_lt] at hst
    apply (S₀_order.2 _ _).2 at hst
    exact eq_of_le_of_ge hst <| Finset.min'_subset (μ_nonempty _) <|
      Set.toFinset_subset_toFinset.mpr <| _μ_mono_right hN le_top
  · intro h
    refine { semistable := fun N hN ↦ ?_ }
    specialize h N hN
    rw [prop3d12 ⟨⊥, N, hN⟩] at h
    simp only [DedekindCut.principal_inj, Finset.singleton_inj] at h
    rw [prop3d12 ⟨⊥, N, hN⟩, prop3d12 (⊤ : StrictIntvl (ℒ R M))]
    simp only [gt_iff_lt, DedekindCut.principal_lt_principal, not_lt]
    exact (S₀_order.2 _ _).1 h.le

/-- Second characterization of semistability: semistable iff unique associated prime.

  Combining `rmk4d14₁` with the explicit formula for `μA`, we show that `Semistable (μ R M)`
  is equivalent to the classical condition `∃! p, p ∈ associatedPrimes R M`.
-/
lemma rmk4d14₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [rmk4d14₁]
  let p0 := ((_μ R M ⊤).toFinset.min' (μ_nonempty _))
  have hbot (N : ℒ R M) : Submodule.submoduleOf (⊥ : ℒ R M) N = ⊥ :=
    Submodule.ker_subtype N
  let eTop :
      (↥(⊤ : ℒ R M) ⧸ Submodule.submoduleOf (⊥ : ℒ R M) ⊤) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ (hbot ⊤)).trans Submodule.topEquiv
  have hp0 : p0.asIdeal ∈ associatedPrimes R M := by
    simpa [LinearEquiv.AssociatedPrimes.eq eTop] using
      min'_asIdeal_mem (⊤ : StrictIntvl (ℒ R M))
  constructor
  · refine fun hs => ⟨p0.asIdeal, hp0, fun J hJ => ?_⟩
    obtain ⟨hJp, t, ht⟩ := (isAssociatedPrime_iff (R := R) (M := M)).1 <|
      (AssociatedPrimes.mem_iff (R := R) (M := M)).1 hJ
    have htors : Ideal.torsionOf R M t = J := by
      ext a
      rw [Ideal.mem_torsionOf_iff, ht, Submodule.mem_colon_singleton, Submodule.mem_bot]
    have hN : ⊥ < (R ∙ t : ℒ R M) := by
      rw [bot_lt_iff_ne_bot, ne_eq, Submodule.span_singleton_eq_bot]
      exact fun ht0 ↦ hJp.ne_top (by rw [ht, ht0, Submodule.colon_singleton_zero])
    have hassN : associatedPrimes R ↥(R ∙ t : ℒ R M) = {J} := by
      rw [← LinearEquiv.AssociatedPrimes.eq (Ideal.quotTorsionOfEquivSpanSingleton R M t), htors,
        associatedPrimes.eq_singleton_of_isPrimary hJp.isPrimary, hJp.radical]
    have hmin : ((_μ R M ⟨⊥, R ∙ t, hN⟩).toFinset.min' (μ_nonempty _)) = ⟨J, hJp⟩ := by
      have hpN : ((_μ R M ⟨⊥, R ∙ t, hN⟩).toFinset.min' (μ_nonempty _)).asIdeal ∈
          associatedPrimes R ↥(R ∙ t : ℒ R M) := by
        simpa [LinearEquiv.AssociatedPrimes.eq
          (Submodule.quotEquivOfEqBot _ (hbot (R ∙ t)))] using
          min'_asIdeal_mem (⟨⊥, R ∙ t, hN⟩ : StrictIntvl (ℒ R M))
      exact PrimeSpectrum.ext (Set.mem_singleton_iff.mp (hassN ▸ hpN))
    have hs' := hs (R ∙ t) hN
    rw [prop3d12 ⟨⊥, R ∙ t, hN⟩] at hs'
    simp only [DedekindCut.principal_inj, Finset.singleton_inj] at hs'
    exact congrArg PrimeSpectrum.asIdeal (hmin.symm.trans hs')
  · rintro ⟨p, hp, hp_unique⟩ N hN
    rw [prop3d12 ⟨⊥, N, hN⟩]
    simp only [DedekindCut.principal_inj, Finset.singleton_inj]
    have hq : (((_μ R M ⟨⊥, N, hN⟩).toFinset.min' (μ_nonempty _)).asIdeal) ∈
      associatedPrimes R M := by
      have hI := _μ_mono_right hN le_top <| min'_asIdeal_mem (⟨⊥, N, hN⟩ : StrictIntvl (ℒ R M))
      simpa [LinearEquiv.AssociatedPrimes.eq eTop] using hI
    exact PrimeSpectrum.ext ((hp_unique _ hq).trans (hp_unique _ hp0).symm)

/--
Admissibility of the slope `μ R M`.

For the coprimary filtration application we only need the “totality” branch of
`μAdmissible`: the codomain order is linear, hence total.
-/
instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
μAdmissible (μ R M) where
  μ_adm := Or.inl inferInstance


/--
Nontriviality of the quotient module for a strict inclusion.

If `N₁ < N₂`, then the quotient `N₂ / N₁` is nontrivial.
-/
lemma quot_ntl {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ : ℒ R M} (hN : N₁ < N₂) : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
  exact hN.not_ge

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
    _μ R M ⟨N₁, W, lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      _μ R (↥N₂ ⧸ N₁.submoduleOf N₂)
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let X := Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)
  have hX : Submodule.submoduleOf (⊥ : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)) X = ⊥ :=
    Submodule.ker_subtype X
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro hp
  · rw [LinearEquiv.AssociatedPrimes.eq
      ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
    simpa [X, hX] using hp
  · rw [← LinearEquiv.AssociatedPrimes.eq
      ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
    simpa [X, hX] using hp

/-- `μA` agrees with the quotient version under the submodule correspondence. -/
lemma muA_eq_quot_muA {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ W : ℒ R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂) (h₃ : W ≠ N₁) :
    μA (μ R M) ⟨N₁, W, lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
        quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
      μA (μ R (↥N₂ ⧸ N₁.submoduleOf N₂))
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) :=
    quot_ntl (lt_of_lt_of_le (lt_of_le_of_ne h₁ (Ne.symm h₃)) h₂)
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
`Semistable` predicate on the quotient lattice; the `Nontrivial` instance for the
quotient is provided by `quot_ntl`.
-/
lemma semistable_res_iff_semistable_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N₁ N₂ : ℒ R M) (hN : N₁ < N₂) :
    Semistable (Resμ ⟨N₁, N₂, hN⟩ (μ R M)) ↔
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := quot_ntl hN
      Semistable (μ R (↥N₂ ⧸ N₁.submoduleOf N₂)) := by
  refine ⟨?_, ?_⟩
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := quot_ntl hN
    refine { semistable := ?_ }
    intro X hX
    have hres := h.semistable
      ⟨lift_quot N₁ N₂ X, lift_quot_middle N₁ N₂ (le_of_lt hN) X⟩
      (bot_lt_iff_ne_bot.2 fun hc ↦
        lift_quot_not_bot N₁ N₂ X hX.ne' (Subtype.coe_inj.mpr hc))
    have hmid := lift_quot_middle N₁ N₂ (le_of_lt hN) X
    have hneq : lift_quot N₁ N₂ X ≠ N₁ := lift_quot_not_bot N₁ N₂ X hX.ne'
    have hres' :
        ¬ μA (μ R M) ⟨N₁, lift_quot N₁ N₂ X, lt_of_le_of_ne hmid.1 hneq.symm⟩ >
          μA (μ R M) ⟨N₁, N₂, hN⟩ := by
      simp only [μA_res_intvl] at hres
      exact hres
    rw [muA_eq_quot_muA hmid.1 hmid.2 hneq,
      muA_eq_quot_muA (le_of_lt hN) le_rfl hN.ne.symm] at hres'
    simpa [lift_quot, Submodule.comap_map_eq, Submodule.ker_subtype,
      Submodule.map_comap_eq_self, Submodule.range_mkQ] using hres'
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := quot_ntl hN
    refine { semistable := ?_ }
    intro W hW
    have hW' : W.val ≠ N₁ := fun hEq ↦ hW.ne' (Subtype.ext hEq)
    have hquot := h.semistable
      (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W.val))
      (bot_lt_iff_ne_bot.2 <| map_comap_ne_bot W.prop.1 W.prop.2 hW')
    have hquot' :
        ¬ μA (μ R M) ⟨N₁, W.val, lt_of_le_of_ne W.prop.1 hW'.symm⟩ >
          μA (μ R M) ⟨N₁, N₂, hN⟩ := by
      simpa [muA_eq_quot_muA (N₁ := N₁) (N₂ := N₂) (W := W.val)
          W.prop.1 W.prop.2 hW',
        muA_eq_quot_muA (N₁ := N₁) (N₂ := N₂) (W := N₂)
          (le_of_lt hN) le_rfl hN.ne.symm,
        Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ] using hquot
    simp only [μA_res_intvl]
    exact hquot'


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
∀ n < HNFil.length,
  Coprimary R (↥(HNFil.filtration (n + 1)) ⧸
    Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) := by
  intro n hn
  let hstep := HNFil.strict_mono hn.le hn (Nat.lt_add_one n)
  let := quot_ntl hstep
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
    HNFil.strict_mono (piecewise_coprimary HNFil) ?_)
  }
  intro n hn p q hp hq
  have := lt_of_not_ge <| HNFil.μA_pseudo_strict_anti n hn
  rw [prop3d12, prop3d12, DedekindCut.principal_lt_principal] at this
  replace this := S₀_order'.2 this
  rw [toLinearExtension_eq_min' ⟨HNFil.filtration (n + 1), HNFil.filtration (n + 2),
      HNFil.strict_mono hn.le hn (Nat.lt_add_one (n + 1))⟩
      (piecewise_coprimary HNFil (n+1) hn).coprimary hp,
    toLinearExtension_eq_min' ⟨HNFil.filtration n, HNFil.filtration (n + 1),
      HNFil.strict_mono (Nat.le_of_succ_le hn.le) (Nat.le_of_succ_le hn) (Nat.lt_add_one n)⟩
      (piecewise_coprimary HNFil n <| Nat.lt_of_succ_lt hn).coprimary hq]
  exact this

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
        let hstep := a.strict_mono hi.le hi (Nat.lt_add_one i)
        let : Nontrivial (↥(a.filtration (i + 1)) ⧸
            Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1))) := quot_ntl hstep
        exact (semistable_res_iff_semistable_quot _ _ hstep).mpr <|
          rmk4d14₂.mpr (a.piecewise_coprimary i hi).coprimary
      · intro i hi
        rw [prop3d12, prop3d12]
        simp only [DedekindCut.principal_le_principal, not_le]
        apply S₀_order'.1
        exact a.strict_anti_associated_prime i hi _ _
          (min'_asIdeal_mem ⟨a.filtration (i + 1), a.filtration (i + 2),
            a.strict_mono hi.le hi (Nat.lt_add_one (i + 1))⟩)
          (min'_asIdeal_mem ⟨a.filtration i, a.filtration (i + 1),
            a.strict_mono (Nat.le_of_succ_le hi.le) (Nat.le_of_succ_le hi) (Nat.lt_add_one i)⟩)
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
    ext
    rw [CoprimaryFiltration.filtration_eq_harderNarasimhan_filtration a,
      ← CoprimaryFiltration.filtration_eq_harderNarasimhan_filtration default]

end impl

end HarderNarasimhan
