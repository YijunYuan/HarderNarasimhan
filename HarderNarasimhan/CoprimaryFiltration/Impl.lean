/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
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

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.OrderTheory.Lex'Order
import HarderNarasimhan.CoprimaryFiltration.AdmittedResults

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

Some classical results are still assumed via `HarderNarasimhan.AdmittedResults`.

API note: most downstream files should import `HarderNarasimhan.CoprimaryFiltration.Results`
instead of this implementation file. This module is large and contains commutative-algebraic
infrastructure.
-/

namespace HarderNarasimhan

namespace impl

/-
Nonemptiness of the finset of associated primes for any strict interval.

For a strict inclusion `N₁ < N₂`, the quotient `N₂ / N₁` is nontrivial, hence it has
at least one associated prime; this yields a nonempty finset `_μ R M I`.
-/
lemma μ_nonempty {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty := by
  intro I
  simp only [Set.toFinset_nonempty]
  haveI : Nontrivial (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2) := by
    rw [Submodule.Quotient.nontrivial_iff, ← lt_top_iff_ne_top]
    have := Classical.byContradiction fun this ↦ (ne_of_lt <| lt_of_lt_of_le I.prop <|
      Submodule.comap_subtype_eq_top.mp <| not_lt_top_iff.1 this) rfl
    exact lt_top_of_lt this
  rcases associatedPrimes.nonempty R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_setOf.mpr ?_⟩
  use q, hq

/-
Lift an annihilator description along an inclusion of submodules.

This technical lemma is used to transport “associated prime given as annihilator of
a cyclic submodule” between quotients.

Given `m` in the quotient `u / N₁` whose annihilator is `p`, and assuming the chosen
representative lies in `N₃`, we produce a corresponding element in `N₃ / N₁` with the
same annihilator.
-/
lemma annihilator_lift {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ u N₃ : Submodule R M} (p : Ideal R)
(m : ↥u ⧸ Submodule.submoduleOf N₁ u)
(hm : p = LinearMap.ker (LinearMap.toSpanSingleton R (↥u ⧸ Submodule.submoduleOf N₁ u) m))
(this : ↑m.out ∈ N₃) :
∃ x, p = LinearMap.ker (LinearMap.toSpanSingleton R (↥N₃ ⧸ Submodule.submoduleOf N₁ N₃) x) := by
  use Submodule.Quotient.mk ⟨m.out, this⟩
  ext y
  constructor
  · intro hy
    rw [hm] at hy
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
    have this': y • (Submodule.Quotient.mk ⟨m.out, this⟩ : ↥N₃ ⧸ Submodule.submoduleOf N₁ N₃) =
      Submodule.Quotient.mk (y • ⟨m.out, this⟩) := rfl
    simp only [this', SetLike.mk_smul_mk, Submodule.Quotient.mk_eq_zero]
    unfold Submodule.submoduleOf
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    replace : y • m.out ∈ N₁.submoduleOf u := by
        apply (Submodule.Quotient.mk_eq_zero _).1
        simp only [Submodule.Quotient.mk_smul]
        unfold Submodule.Quotient.mk
        simp only [Quotient.out_eq, hy]
    exact this
  · intro hy
    rw [hm]
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
    apply (Submodule.Quotient.mk_eq_zero _).1 at hy
    simp only [SetLike.mk_smul_mk] at hy
    replace hy : Submodule.Quotient.mk ((y • Quotient.out m): ↥u) =
      (0 : ↥u ⧸ Submodule.submoduleOf N₁ u) := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact hy
    apply (Submodule.Quotient.mk_eq_zero _).1 at hy
    have : (⟦Quotient.out (y • m)⟧ : ↥u ⧸ Submodule.submoduleOf N₁ u) = ⟦y • Quotient.out m⟧ := by
      simp only [Quotient.out_eq]
      nth_rw 1 [← Quotient.out_eq m]
      exact rfl
    rw [← Quotient.out_eq (y • m), this]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy

  /-
  Monotonicity of `_μ` in the right endpoint.

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
  intro i w
  unfold _μ at *
  simp only [Set.mem_setOf_eq] at *
  rcases w with ⟨p,⟨hp1,hp2⟩⟩
  rw [← hp2]
  use p
  simp only [exists_prop, and_true]
  unfold associatedPrimes at *
  simp only [Set.mem_setOf_eq] at *
  unfold IsAssociatedPrime at *
  refine ⟨hp1.1,?_⟩
  simp only [Set.mem_setOf_eq] at hp1
  rcases hp1.2 with ⟨m,hm⟩
  rw [Submodule.bot_colon'] at hm
  simp only [Submodule.bot_colon']
  have hm : p = (LinearMap.toSpanSingleton R (↥u ⧸ N₁.submoduleOf u) m).ker := by
    rw [hm]
    ext z
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply Submodule.mem_annihilator_span_singleton
  rcases (annihilator_lift p m hm <| (Submodule.Quotient.mk_eq_zero N₃).mp
    (by rw [Submodule.Quotient.mk_eq_zero]; exact h₂ m.out.prop)) with ⟨P, hP⟩
  use P
  rw [hP]
  ext z
  simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  exact Iff.symm (Submodule.mem_annihilator_span_singleton P z)


/-
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
  · simp only [ne_eq, Set.mem_setOf_eq]
    use I.val.2
    use ⟨⟨le_of_lt I.prop,le_rfl⟩,ne_of_lt I.prop⟩
  · apply mem_upperBounds.2
    intro x hx
    simp only [ne_eq, Set.mem_setOf_eq] at hx
    rcases hx with ⟨u,⟨hu1,hu2⟩⟩
    rw [← hu2]
    unfold μ
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      OrderEmbedding.le_iff_le]
    apply S₀_order.1
    exact Set.toFinset_subset_toFinset.mpr <| _μ_mono_right (lt_of_le_of_ne hu1.1.1 hu1.2) hu1.1.2

/-
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
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.le_iff_le]
  refine S₀_order.1 (_μ R M ⟨(x ⊓ y, x), inf_lt_left.mpr hxy⟩).toFinset
    (_μ R M ⟨(y, x ⊔ y), right_lt_sup.mpr hxy⟩).toFinset (Set.toFinset_subset_toFinset.mpr ?_)
  unfold _μ
  intro w hw
  simp only [Set.mem_setOf_eq] at *
  rcases hw with ⟨p,⟨hp1,hp2⟩⟩
  use p
  simp only [hp2, exists_prop, and_true]
  apply AssociatePrimes.mem_iff.2
  apply AssociatePrimes.mem_iff.1 at hp1
  refine ⟨hp1.1,?_⟩
  rcases hp1.2 with ⟨m,hm⟩
  use (LinearMap.quotientInfEquivSupQuotient _ _).toFun m
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  rw [hm]
  ext r
  have := Eq.symm (LinearEquiv.map_smul (LinearMap.quotientInfEquivSupQuotient x y) r m)
  constructor
  · intro h
    simp only at *
    rw [Submodule.bot_colon', Submodule.mem_annihilator_span_singleton, this] at *
    simp only [h, map_zero]
  · intro h
    simp only at *
    rw [Submodule.bot_colon', Submodule.mem_annihilator_span_singleton, this] at *
    exact (LinearEquiv.map_eq_zero_iff (LinearMap.quotientInfEquivSupQuotient x y)).mp h

/-
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
  rcases hx with ⟨p,m,hpm⟩
  use m
  simp only [hpm]
  intro z hz
  rw [Submodule.bot_colon']
  exact hz

/-
Monotonicity of support under enlarging the submodule being quotiented out.

If `N₁ ≤ N₂`, then the support of `N₃ / N₂` is contained in the support of
`N₃ / N₁`. This is a standard “support shrinks under quotients” statement.
-/
lemma support_quotient_mono {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(N₁ N₂ N₃ : Submodule R M) (h : N₁ ≤ N₂) :
  Module.support R (N₃⧸ N₂.submoduleOf N₃) ⊆ Module.support R (N₃⧸ N₁.submoduleOf N₃) := by
  intro p hp
  simp only [Module.mem_support_iff_exists_annihilator] at *
  rcases hp with ⟨m,hm⟩
  use Submodule.Quotient.mk m.out
  intro z hz
  have : z • (Submodule.Quotient.mk m.out : ↥N₃ ⧸ N₁.submoduleOf N₃)= 0 :=
    (Submodule.mem_annihilator_span_singleton (Submodule.Quotient.mk (Quotient.out m)) z).mp hz
  replace : z ∈ (Submodule.span R {m}).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton]
    rw [← Submodule.Quotient.mk_smul] at this
    apply (Submodule.Quotient.mk_eq_zero _).1 at this
    have this' : z • m = Submodule.Quotient.mk (z • m).out := by
      unfold Submodule.Quotient.mk Quotient.mk''
      rw [Quotient.out_eq]
    rw [this']
    apply (Submodule.Quotient.mk_eq_zero _).2
    replace this' : z • m.out - (z • m).out ∈ N₂.submoduleOf N₃ := by
      apply (Submodule.Quotient.mk_eq_zero _).1
      simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      unfold Submodule.Quotient.mk Quotient.mk''
      rw [Quotient.out_eq, Quotient.out_eq, sub_self]
    exact (Submodule.sub_mem_iff_right (N₂.submoduleOf N₃) (h this)).mp this'
  exact hm this

/-
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

/-
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
  rw [← AdmittedResults.min_associated_prime_iff_min_supp] at hr
  refine le_trans ?_ <| toLinearExtension.monotone' hr'
  refine (((_μ R M) I).toFinset.min'_le) r ?_
  simp only [Set.mem_toFinset, Set.mem_setOf_eq]
  use r.asIdeal, hr.1


/-
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
      simp only [Finset.mem_val, Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rwa [← hp2]
    exact prop3d12p1 I N'' ha1 (((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'
      <| μ_nonempty _).asIdeal) this'
  refine le_trans this ?_
  apply S₀_order.1
  simp only [Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
  exact Set.mem_toFinset.mp <|
    (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty _

/-
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

  /-
  Quotient map used in the `μA` computation.

  `CP.f2 I` is the linear map `I.val.2 → I.val.2 / I.val.1`.
  -/
abbrev CP.f2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
I.val.2 →ₗ[R] (I.val.2⧸I.val.1.submoduleOf I.val.2) where
  toFun := fun x : I.val.2 ↦ (I.val.1.submoduleOf I.val.2).mkQ x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-
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

/-
Mapping a submodule of `N` to a submodule of `M` and restricting back.

This is a small bookkeeping lemma about `Submodule.map`/`submoduleOf` used to simplify
some of the quotient arguments below.
-/
lemma submoduleOf_map_subtype {R : Type*} [CommRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M]
(N : Submodule R M) (N' : Submodule R ↥N) : N' = (Submodule.map (N.subtype) N').submoduleOf N := by
  ext z
  constructor
  · intro hz
    use z
    simpa only [SetLike.mem_coe, Submodule.subtype_apply, and_true]
  · intro hz
    rcases hz with ⟨y,hy1,hy2⟩
    simp only [Submodule.subtype_apply, SetLike.coe_eq_coe] at hy2
    exact hy2 ▸ hy1

  /-
  An isomorphism rewriting a quotient by `ker_of_quot_comp_localization`.

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
  have := (@Submodule.quotientQuotientEquivQuotient R  (I.val.2) _ _ _ (I.val.1.submoduleOf I.val.2)
    ((Submodule.map (Submodule.subtype I.val.2)
    (LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I))).submoduleOf I.val.2) (by
    intro z hz
    rw [← submoduleOf_map_subtype I.val.2 (LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I))]
    rw [LinearMap.mem_ker]
    have : (CP.f2 I) z = 0 := by
      unfold CP.f2
      simp only [Submodule.mkQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rwa [Submodule.Quotient.mk_eq_zero]
    rw [LinearMap.comp_apply,this]
    simp only [LocalizedModule.mkLinearMap_apply, OreLocalization.zero_oreDiv]
    )).symm
  have t : Submodule.map (Submodule.submoduleOf I.val.1 I.val.2).mkQ
      ((Submodule.map (Submodule.subtype I.val.2)
      (LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I))).submoduleOf I.val.2) = LinearMap.ker (CP.f1 I) := by
      ext z
      simp only [Submodule.mem_map, Submodule.mkQ_apply, Subtype.exists, LinearMap.mem_ker]
      constructor
      · intro hz
        rcases hz with ⟨y,hy1,hy2,hy3⟩
        have hy2 : y ∈ Submodule.map (Submodule.subtype I.val.2)
          (LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I)) := hy2
        simp only [Submodule.mem_map, LinearMap.mem_ker] at hy2
        rcases hy2 with ⟨w,hw1,hw2⟩
        have : Submodule.Quotient.mk ⟨y, hy1⟩ = (CP.f2 I) w := by
          simp only [← hw2, Submodule.subtype_apply, Subtype.coe_eta, LinearMap.coe_mk,
            Submodule.mkQ_apply, AddHom.coe_mk]
        rwa [← hy3, this]
      · intro hz
        use z.out.val, Submodule.coe_mem z.out
        simp only [Subtype.coe_eta]
        constructor
        · have : z.out ∈ LinearMap.ker (CP.f1 I ∘ₗ CP.f2 I) := by
            simp only [LinearMap.mem_ker]
            have : (CP.f2 I) z.out = z := by
              unfold CP.f2
              simp only [Submodule.mkQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
              unfold Submodule.Quotient.mk Quotient.mk''
              rw [Quotient.out_eq]
            rwa [← this] at hz
          convert this
          rw [← submoduleOf_map_subtype]
        · unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
  use t ▸ this

/-
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
  have := AdmittedResults.bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6
    ((((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl) (LinearMap.ker (CP.f1 I))
  simp only [iff_true] at this
  rw [this.2]
  ext q
  constructor
  · intro hq
    simp only [Set.mem_setOf_eq] at hq
    simp only [Set.mem_singleton_iff]
    replace := ((_μ R M) I).toFinset.min'_le {asIdeal := q, isPrime := hq.1.out.1} (by
      simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      use q, hq.1)
    simp only [eq_of_le_of_ge this <| toLinearExtension.monotone' <| Set.diff_eq_empty.mp hq.2]
  · intro hq
    simp only [Set.sdiff_sep_self, Set.mem_singleton_iff,
      Set.mem_setOf_eq] at *
    rw [hq]
    constructor
    · replace := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨_,⟨hp1,hp2⟩⟩
      exact hp2 ▸ hp1
    · unfold Ideal.primeCompl
      simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.inter_compl_self]

/-
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
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  unfold μA
  simp only [μmax_eq_μ, ne_eq]
  unfold μ
  have res1 : (OrderTheory.coe' {(_μ R M I).toFinset.min' (μ_nonempty I)} : S R) ∈
    {x | ∃ a, ∃ (h : InIntvl I a ∧ ¬a = I.val.2), OrderTheory.coe'
    (_μ R M ⟨(a, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩).toFinset = x} := by
    simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq]
    use ker_of_quot_comp_localization I
    constructor
    · conv_lhs => unfold _μ
      simp only [associated_primes_quot_koqcl I, Set.mem_singleton_iff, exists_prop_eq,
        Set.setOf_eq_eq_singleton', Set.toFinset_singleton, Finset.singleton_inj]
      rfl
    · constructor
      · constructor
        · unfold ker_of_quot_comp_localization
          intro z hz
          simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk,
            AddHom.coe_mk, Function.comp_apply, Submodule.subtype_apply, Subtype.exists,
            exists_and_right, exists_eq_right]
          use (le_of_lt I.prop) hz
          have : Submodule.Quotient.mk ⟨z, (Iff.of_eq (Eq.refl (z ∈ I.val.2))).mpr
            (le_of_lt (Subtype.prop I) hz) ⟩ =
            (0 : ↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2)
            := by simpa only [Submodule.Quotient.mk_eq_zero]
          simp only [Submodule.mkQ_apply, this, LocalizedModule.mkLinearMap_apply,
            LocalizedModule.zero_mk]
        · unfold ker_of_quot_comp_localization
          simp only [Submodule.map_subtype_le]
      · by_contra hc
        have := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
        simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
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
          push_neg at hc
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
            Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk,
            Submodule.mkQ_apply, AddHom.coe_mk, Function.comp_apply, Submodule.subtype_apply,
            SetLike.coe_eq_coe, exists_eq_right] at *
          exact this
        unfold CP.f2 at this'
        simp only [Submodule.mkQ_apply, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
          Function.comp_apply] at this'
        unfold Submodule.Quotient.mk Quotient.mk'' at this'
        rw [Quotient.out_eq] at this'
        exact hm this'
  apply IsLeast.csInf_eq
  refine ⟨res1,?_⟩
  apply mem_lowerBounds.2
  intro N hN
  rcases hN with ⟨a,ha1,ha2⟩
  rw [← ha2]
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.le_iff_le]
  exact prop3d12p2 I a ha1.1 ha1.2

/--
Proposition 3.13 (part 1): the strict order on `ℒ R M` is well-founded.

This provides the `WellFoundedGT` instance needed for the general Harder–Narasimhan
filtration machinery.
-/
instance prop3d13₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
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
    simp only [prop3d12, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding] at hc
    simp only [OrderEmbedding.lt_iff_lt, not_lt, not_le] at hc
    have hc := fun w ↦ S₀_order'.mpr (by
      simpa only [OrderEmbedding.lt_iff_lt] using (hc w)
      )
    have s1 : ∀ i, ((_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min' <| μ_nonempty _).asIdeal ∈
      associatedPrimes R ((x i)⧸(Submodule.submoduleOf N (x i))) := by
      intro i
      have := (_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min'_mem (μ_nonempty _)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨_,⟨_,hp2⟩⟩
      rwa [← hp2]
    have s2 : ∀ i, associatedPrimes R (↥(x i) ⧸ Submodule.submoduleOf N (x i)) ⊆ associatedPrimes R
      (↥(x 0) ⧸ Submodule.submoduleOf N (x 0)) := by
      intro i w hw'
      unfold associatedPrimes at *
      simp only [Set.mem_setOf_eq] at *
      unfold IsAssociatedPrime at *
      refine ⟨hw'.1,?_⟩
      rcases hw'.2 with ⟨m,hm⟩
      have : ↑(Quotient.out m) ∈ x 0 := by
        if hi : i = 0 then
          rw [← hi]
          exact Submodule.coe_mem m.out
        else
        have hx2 := subset_of_ssubset <| (hx2 (Nat.zero_lt_of_ne_zero hi)).ssubset
        exact hx2 <| Submodule.coe_mem m.out
      have hm : w = (LinearMap.toSpanSingleton R (↥(x i) ⧸ Submodule.submoduleOf N (x i)) m).ker
      := by
        rw [hm]
        ext z
        simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, LinearMap.mem_ker,
          LinearMap.toSpanSingleton_apply]
      rcases (annihilator_lift w m hm this) with ⟨P, hP⟩
      use P
      rw [hP]
      ext z
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Submodule.mem_colon_singleton,
        Submodule.mem_bot]
    have : (associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0))).Infinite := by
      refine Set.infinite_of_injective_forall_mem ?_ <| fun i ↦ s2 i (s1 i)
      intro a b hab
      by_contra!
      have help : ∀ A B : LinearExtension (PrimeSpectrum R), A.asIdeal = B.asIdeal → A = B :=
            fun A B h ↦ id (PrimeSpectrum.ext (Ideal.ext
              fun t ↦ Eq.to_iff (congrFun (congrArg Membership.mem h) t)))
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

/-
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
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    rw [prop3d12 ⟨(⊥,N),hN⟩, prop3d12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩] at hst
    rw [prop3d12 ⟨(⊥,N),hN⟩]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, gt_iff_lt,
      OrderEmbedding.lt_iff_lt, not_lt] at hst
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
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj] at h
    rw [t1,t2]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, gt_iff_lt,
      OrderEmbedding.lt_iff_lt, not_lt, ge_iff_le]
    apply (S₀_order.2 _ _).1
    rw [h]

set_option maxHeartbeats 60000 in
  /- Increased heartbeat limit: this proof is large and uses heavy algebraic rewriting. -/
  /-
  Second characterization of semistability: semistable iff unique associated prime.

  Combining `rmk4d14₁` with the explicit formula for `μA`, we show that `Semistable (μ R M)`
  is equivalent to the classical condition `∃! p, p ∈ associatedPrimes R M`.
  -/
lemma rmk4d14₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [rmk4d14₁]
  constructor
  · intro h
    have := prop3d12 (⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩)
    use ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min' <| μ_nonempty _).asIdeal
    constructor
    · simp only
      have := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_mem <| μ_nonempty _
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := Submodule.quotEquivOfEqBot (Submodule.submoduleOf (⊥: Submodule R M)
        (⊤: Submodule R M)) (id (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥)
        (Submodule.ker_subtype ⊤)) (eq_self ⊥))))
      exact LinearEquiv.trans t1 Submodule.topEquiv
    · intro J hJ
      by_contra hc
      replace := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_le ⟨J,hJ.out.1⟩ (by
        simp only [Set.mem_toFinset, Set.mem_setOf_eq]
        use J
        simp only [exists_prop, and_true]
        convert hJ
        refine LinearEquiv.AssociatedPrimes.eq <| ?_
        have t1 := Submodule.quotEquivOfEqBot (Submodule.submoduleOf (⊥: Submodule R M)
          (⊤: Submodule R M)) (id (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥)
          (Submodule.ker_subtype ⊤)) (eq_self ⊥))))
        exact LinearEquiv.trans t1 Submodule.topEquiv
        )
      simp only at this
      unfold associatedPrimes IsAssociatedPrime at hJ
      simp only [Set.mem_setOf_eq] at hJ
      rcases hJ.2 with ⟨t,ht⟩
      let N := Submodule.span R {t}
      have hN : ⊥ < N := by
        by_contra hc
        simp only [not_bot_lt_iff] at hc
        rw [Submodule.span_singleton_eq_bot.mp hc] at ht
        exact Ideal.IsPrime.ne_top (ht ▸ hJ).1 Submodule.colon_singleton_zero
      specialize h N hN
      rw [prop3d12 ⟨(⊥, N), hN⟩] at h
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj] at h
      rw [← h] at hc
      replace : (_μ R M ⟨(⊥, N), hN⟩) = {⟨J,hJ.1⟩} := by
        unfold _μ
        simp only
        ext s
        constructor
        · intro hs
          simp only [Set.mem_setOf_eq] at hs
          simp only [Set.mem_singleton_iff]
          rcases hs with ⟨p,⟨hp1,hp2⟩⟩
          have : p = J := by
            unfold associatedPrimes IsAssociatedPrime at hp1
            simp only [Set.mem_setOf_eq] at hp1
            replace hp1 := hp1.2
            rcases hp1 with ⟨s,hs⟩
            rw [hs, ht]
            apply Eq.symm
            refine Submodule.ext ?_
            intro g
            constructor
            · intro hg
              simp only at *
              let s' : M:= N.subtype s.out
              have hs' : s' ∈ N := by
                unfold s'
                simp only [Submodule.subtype_apply, SetLike.coe_mem]
              rcases (@Submodule.mem_span_singleton R M _ _ _ s' t).1 hs' with ⟨r₀,hr₀⟩
              have hfinal : g • s' = 0 := by
                rw [← hr₀,← smul_assoc]
                nth_rw 1 [smul_eq_mul]
                rw [CommRing.mul_comm,← smul_eq_mul,smul_assoc]
                simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at hg
                simp only [hg, smul_zero]
              unfold s' at hfinal
              simp only [Submodule.subtype_apply] at hfinal
              have hfinal' : (g • ↑(Quotient.out s) : M) = ↑(g • Quotient.out s) := rfl
              replace hfinal : g • Quotient.out s = 0 :=
                Submodule.coe_eq_zero.mp <| hfinal' ▸ hfinal
              have : (⟦g • Quotient.out s⟧ : ↥N ⧸ Submodule.submoduleOf ⊥ N) =
                g • (Submodule.Quotient.mk (Quotient.out s)) := by rfl
              rw [hfinal] at this
              unfold Submodule.Quotient.mk Quotient.mk'' at this
              rw [Quotient.out_eq] at this
              simp only [Submodule.mem_colon_singleton, ← this, Submodule.mem_bot]
              rfl
            · intro hg
              simp only at *
              let s' : M := N.subtype s.out
              have s'_ne0 : s' ≠ 0 := by
                by_contra hc
                unfold s' at hc
                simp only [Submodule.subtype_apply, ZeroMemClass.coe_eq_zero] at hc
                have : s = 0 := by
                  have := hc ▸ Quotient.out_eq s
                  exact id (Eq.symm this)
                rw [this, Submodule.bot_colon'] at hs
                simp only [Submodule.span_zero_singleton, Submodule.annihilator_bot] at hs
                exact (Ideal.IsPrime.ne_top hp1.1) hs
              have hs' : g • s' = 0 := by
                unfold s'
                simp only [Submodule.subtype_apply]
                rw [((by rfl) : g • (↑(Quotient.out s) : M) = ↑(g • Quotient.out s))]
                refine ZeroMemClass.coe_eq_zero.mpr ?_
                have : (⟦g • Quotient.out s⟧ : ↥N ⧸ Submodule.submoduleOf ⊥ N) =
                  g • (Submodule.Quotient.mk (Quotient.out s)) := rfl
                unfold Submodule.Quotient.mk Quotient.mk'' at this
                simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at hg
                rw [Quotient.out_eq, hg] at this
                have this' : (Submodule.Quotient.mk (g • Quotient.out s) :
                  ↥N ⧸ Submodule.submoduleOf ⊥ N) = ⟦g • Quotient.out s⟧ := by rfl
                exact Submodule.coe_eq_zero.mp <|
                  (Submodule.Quotient.mk_eq_zero _).1 <| this' ▸ this
              have hst : s' ∈ Submodule.span R {t} := by
                unfold s'
                simp only [Submodule.subtype_apply, SetLike.coe_mem]
              rcases (@Submodule.mem_span_singleton R M _ _ _ s' t).1 hst with ⟨r₀,hr₀⟩
              rw [← hr₀,← smul_assoc] at hs'
              have : (g • r₀) ∈ J := by
                rw [ht]
                simp only [smul_eq_mul, Submodule.mem_colon_singleton, Submodule.mem_bot]
                rw [← smul_eq_mul,hs']
              rw [smul_eq_mul] at this
              rcases hJ.1.mul_mem_iff_mem_or_mem.1 this with this | this
              · rw [ht] at this
                simpa only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using this
              · rw [ht] at this
                simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at this
                rw [hr₀] at this
                exact False.elim <| s'_ne0 this
          simp only [← hp2, this]
        · intro hs
          simp only [Set.mem_singleton_iff] at hs
          simp only [Set.mem_setOf_eq]
          use s.asIdeal
          simp only [hs, exists_prop, and_true]
          unfold associatedPrimes IsAssociatedPrime
          simp only [Set.mem_setOf_eq]
          refine ⟨IsAssociatedPrime.isPrime hJ,?_⟩
          use Submodule.Quotient.mk ⟨t,Submodule.mem_span_singleton_self t⟩
          rw [ht]
          refine Submodule.ext ?_
          intro g
          constructor
          · intro hg
            simp only at *
            have : ((g • Submodule.Quotient.mk (⟨t, Submodule.mem_span_singleton_self t⟩: ↥N)) :
              ↥N ⧸ Submodule.submoduleOf ⊥ N) = Submodule.Quotient.mk
              (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) := rfl
            simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at hg
            simp only [Submodule.mem_colon_singleton, this, SetLike.mk_smul_mk, hg,
              Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
            subst ht hs
            simp_all only [SetLike.mk_smul_mk, N]
            obtain ⟨left, right⟩ := hJ
            obtain ⟨w, h_1⟩ := right
            simp_all only
            rfl
          · intro hg
            simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at *
            have : ((g • Submodule.Quotient.mk (⟨t, Submodule.mem_span_singleton_self t⟩: ↥N)) :
              ↥N ⧸ Submodule.submoduleOf ⊥ N) = Submodule.Quotient.mk
              (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) := rfl
            rw [hg] at this
            have this' : (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) =
              ( ⟨g • t,  Submodule.smul_mem N g <| Submodule.mem_span_singleton_self t⟩ : ↥N) := rfl
            simp only [this'] at this
            exact (Submodule.Quotient.mk_eq_zero _).1 this.symm
      simp only [this, Set.toFinset_singleton, Finset.min'_singleton, not_true_eq_false] at hc
  · intro h N hN
    rw [prop3d12 (⟨(⊥, N), hN⟩)]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
    have : (_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty _) ∈ _μ R M ⟨(⊥, ⊤), bot_lt_top⟩ := by
      refine (_μ_mono_right hN le_top) ?_
      simp only [Set.mem_setOf_eq]
      have := (_μ R M ⟨(⊥, N), hN⟩).toFinset.min'_mem (μ_nonempty _)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨t1,_⟩
      use t1
    simp only [Set.mem_setOf_eq] at this
    rcases this with ⟨p,⟨hp1,hp2⟩⟩
    replace hp1 : p ∈ associatedPrimes R M := by
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _ (Submodule.submoduleOf
        (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
      exact LinearEquiv.trans t1 Submodule.topEquiv
    have hp1' : ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min' (μ_nonempty _)).asIdeal ∈
      associatedPrimes R M := by
      have := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_mem (μ_nonempty _)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _
        (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
      exact LinearEquiv.trans t1 Submodule.topEquiv
    simp only [← hp2, h.unique hp1 hp1']
    rfl

/-
Admissibility of the slope `μ R M`.

For the coprimary filtration application we only need the “totality” branch of
`μ_Admissible`: the codomain order is linear, hence total.
-/
instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
μ_Admissible (μ R M) where
  μ_adm := Or.inl inferInstance

/-
Lift a submodule of a quotient back to a submodule of the ambient module.

Given `x ≤ N₂ / N₁`, we define `lift_quot N₁ N₂ x` as the preimage of `x` under the
quotient map `N₂ → N₂ / N₁`, mapped into `M` via the subtype inclusion `N₂ ↪ M`.

This is used to relate semistability of a restricted slope (on an interval) to
semistability of the induced slope on the quotient lattice.
-/
open Classical in
def lift_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : Submodule R M)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) : Submodule R M :=
  Submodule.map N₂.subtype (Submodule.comap (N₁.submoduleOf N₂).mkQ x)

/-
Basic bounds for `lift_quot`.

If `N₁ ≤ N₂`, then `N₁ ≤ lift_quot N₁ N₂ x ≤ N₂` for any submodule `x` of the
quotient `N₂ / N₁`.
-/
lemma lift_quot_middle {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) :
N₁ ≤ lift_quot N₁ N₂ x ∧ lift_quot N₁ N₂ x ≤ N₂ := by
  constructor
  · intro x' hx
    unfold lift_quot
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right]
    use hN hx
    convert Submodule.zero_mem x
    simpa only [Submodule.Quotient.mk_eq_zero]
  · unfold lift_quot
    intro x' hx
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right] at hx
    exact hx.choose

  /-
  Nontriviality is preserved by `lift_quot`.

  If `x ≠ ⊥` as a submodule of the quotient `N₂ / N₁`, then the lifted submodule
  `lift_quot N₁ N₂ x` is not equal to `N₁`.
  -/
lemma lift_quot_not_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M)
(x : Submodule R (N₂ ⧸ (N₁.submoduleOf N₂))) (hx : x ≠ ⊥) : lift_quot N₁ N₂ x ≠ N₁:= by
  by_contra hc
  refine hx ?_
  unfold lift_quot at hc
  refine (Submodule.eq_bot_iff x).mpr ?_
  intro r hr
  rcases (Quotient.exists_rep r) with ⟨rtilde,hrtilde⟩
  have : N₂.subtype rtilde ∈ N₁ := by
    rw [← hc]
    simp only [Submodule.subtype_apply, Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply,
      SetLike.coe_eq_coe, exists_eq_right]
    convert hr
  rw [← hrtilde]
  apply (Submodule.Quotient.mk_eq_zero (N₁.submoduleOf N₂)).2
  exact this

/-
Nontriviality of the quotient module for a strict inclusion.

If `N₁ < N₂`, then the quotient `N₂ / N₁` is nontrivial.
-/
lemma quot_ntl {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ : ℒ R M} (hN : N₁ < N₂) : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [Submodule.Quotient.nontrivial_iff]
  by_contra hc
  have h' : ∀ x ∈ N₂, x ∈ N₁ := by
    intro x hx
    have : ⟨x,hx⟩ ∈ Submodule.submoduleOf N₁ N₂ := hc ▸ Submodule.mem_top
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at this
    exact this
  exact (not_lt_of_ge h') <| hN

/-
Nontriviality of the induced submodule lattice on the quotient.

This is the corresponding `Nontrivial` instance for the submodule lattice
`ℒ R (N₂ / N₁)`.
-/
lemma quot_ntl' {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ N₂ : ℒ R M} (hN : N₁ < N₂) :
Nontrivial (@ℒ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _)
:= (Submodule.nontrivial_iff R).mpr <| (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)



/-
Membership transfer for mapped submodules.

If `x ∈ Submodule.map N.subtype N'`, then the corresponding element of `N` lies in
`N'`. This is a small helper for arguments involving `Submodule.map`.
-/
lemma Submodule.mem_map_subtype_iff {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(N : Submodule R M) (N' : Submodule R ↥N)
(x : M) (hx1 : x ∈ N) (hx2 : x ∈ Submodule.map N.subtype N')
: ⟨x,hx1⟩ ∈ N' := by
  simp only [Submodule.mem_map, Submodule.subtype_apply, Subtype.exists, exists_and_right,
    exists_eq_right] at hx2
  rcases hx2 with ⟨a,b⟩
  exact b

set_option maxHeartbeats 700000 in
/- Increased heartbeat limit: this proof transports semistability across quotients. -/
/-
Semistability of a restriction vs. semistability on the quotient lattice.

This lemma is the key “translation” step for coprimary filtrations:

* restricting the slope `μ R M` to an interval `(N₁, N₂)` corresponds to
* the induced slope on the submodule lattice of the quotient module `N₂ / N₁`.

The statement is phrased as an equivalence between `Semistable (Resμ ...)` and a
`Semistable` predicate on the quotient lattice, with all required `Nontrivial`
instances provided by `quot_ntl`/`quot_ntl'`.
-/
open Classical in
lemma semistable_res_iff_semistable_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : ℒ R M) (hN : N₁ < N₂) :
Semistable (Resμ ⟨(N₁, N₂), hN⟩ (μ R M)) ↔
@Semistable (@ℒ R _ _ (↥N₂ ⧸ N₁.submoduleOf N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)  _ _ _)
  (@quot_ntl' R _ _ M _ _ _ _ N₁ N₂ hN) _ _ (S R) _
  (@μ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _) := by
  refine ⟨fun h ↦ ?_,fun h ↦ ?_⟩
  · replace h := h.semistable
    have : Nontrivial (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) := quot_ntl hN
    replace : Nontrivial (ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := quot_ntl' hN
    refine {semistable := ?_ }
    intro W hW
    specialize h ⟨(lift_quot N₁ N₂ W),(lift_quot_middle N₁ N₂  <| le_of_lt hN) W ⟩
      (fun hc ↦ lift_quot_not_bot N₁ N₂ W hW (Subtype.coe_inj.mpr hc))
    convert h
    · rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, W), bot_lt_iff_ne_bot.mpr hW⟩ =
        _μ R M ⟨(↑(⊥ : Interval ⟨(N₁, N₂), hN⟩), lift_quot N₁ N₂ W), by
        refine lt_of_le_of_ne ?_ ?_
        · apply (lift_quot_middle _ _ _ _).1
          exact le_of_lt hN
        · apply Ne.symm <| lift_quot_not_bot N₁ N₂ W hW
        ⟩ := by
        unfold _μ
        simp only
        ext x
        constructor
        · intro hx
          simp only [gt_iff_lt, not_lt, Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have wp : N₂.subtype (W.subtype q.out).out ∈ lift_quot N₁ N₂ W := by
            unfold lift_quot
            simp only [Submodule.subtype_apply, Submodule.mem_map, Submodule.mem_comap,
              Submodule.mkQ_apply, SetLike.coe_eq_coe, exists_eq_right]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
            apply SetLike.coe_mem
          use ((N₁).submoduleOf (lift_quot N₁ N₂ W)).mkQ ⟨N₂.subtype (W.subtype q.out).out,wp⟩
          simp only [Submodule.subtype_apply, Submodule.mkQ_apply]
          ext z
          simp only [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top,
            Submodule.mem_colon_singleton, Submodule.mem_bot] at *
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          constructor
          · intro hz
            have : z • (↑(Quotient.out (↑(Quotient.out q) :
              ↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) : M) ∈ N₁ := by
              have : z • Quotient.out (Quotient.out q).val ∈ N₁.submoduleOf N₂ := by
                have : z • Quotient.out (Quotient.out q).val -
                  Quotient.out (z • Quotient.out q).val ∈ Submodule.submoduleOf N₁ N₂ := by
                  apply (Submodule.Quotient.mk_eq_zero _).1
                  simp only [SetLike.val_smul, Submodule.Quotient.mk_sub,
                    Submodule.Quotient.mk_smul]
                  unfold Submodule.Quotient.mk Quotient.mk''
                  simp only [Quotient.out_eq, sub_self]
                have this' : Quotient.out (z • Quotient.out q).val ∈
                  Submodule.submoduleOf N₁ N₂ := by
                  have : z • q.out = 0 := by
                    rw [← Quotient.out_eq (z • q)] at hz
                    apply (Submodule.Quotient.mk_eq_zero _).1 at hz
                    replace : Submodule.submoduleOf ⊥ W = ⊥ := by
                      unfold Submodule.submoduleOf
                      simp only [Submodule.comap_bot, Submodule.ker_subtype]
                    simp only [this, Submodule.mem_bot] at hz
                    rw [← hz]
                    replace : z • q.out - (z • q).out ∈ (⊥: Submodule R ↥W) := by
                      rw [← this]
                      apply (Submodule.Quotient.mk_eq_zero _).1
                      simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
                      unfold Submodule.Quotient.mk Quotient.mk''
                      simp only [Quotient.out_eq, sub_self]
                    simp only [Submodule.mem_bot] at this
                    exact sub_eq_zero.1 this
                  rw [this]
                  simp only [ZeroMemClass.coe_zero]
                  apply (Submodule.Quotient.mk_eq_zero _).1
                  unfold Submodule.Quotient.mk Quotient.mk''
                  apply Quotient.out_eq
                exact (Submodule.sub_mem_iff_left (Submodule.submoduleOf N₁ N₂) this').mp this
              exact this
            exact this
          · intro hz
            replace hz : z • (Quotient.out (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ := hz
            replace : z • Quotient.out (Quotient.out q).val -
              Quotient.out (z • (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ := by
              apply (Submodule.Quotient.mk_eq_zero _).1
              simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
              unfold Submodule.Quotient.mk Quotient.mk''
              simp only [Quotient.out_eq]
              apply sub_self
            replace hz : Quotient.out (z • (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ :=
              (Submodule.sub_mem_iff_right (Submodule.submoduleOf N₁ N₂) hz).mp this
            replace hz : z • (Quotient.out q).val = 0 := by
              apply (Submodule.Quotient.mk_eq_zero _).2 at hz
              unfold Submodule.Quotient.mk Quotient.mk'' at hz
              simpa only [Quotient.out_eq] using hz
            have hz : z • q.out = 0 := Submodule.coe_eq_zero.mp hz
            apply_fun (Submodule.submoduleOf ⊥ W).mkQ at hz
            simp only [map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at hz
            unfold Submodule.Quotient.mk Quotient.mk'' at hz
            simpa only [Quotient.out_eq] using hz
        · intro hx
          simp only [gt_iff_lt, not_lt, Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          replace : q.out.val ∈ N₂ := by
            have : lift_quot N₁ N₂ W ≤ N₂ := Submodule.map_subtype_le N₂
              (Submodule.comap (Submodule.submoduleOf N₁ N₂).mkQ W)
            exact this q.out.prop
          have this' : (N₁.submoduleOf N₂).mkQ ⟨q.out.val,this⟩ ∈ W :=
            Submodule.mem_map_subtype_iff N₂ ((Submodule.comap (Submodule.submoduleOf N₁ N₂).mkQ W))
            q.out.val this q.out.prop
          use ((⊥ : Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf W).mkQ
            (⟨(N₁.submoduleOf N₂).mkQ ⟨q.out.val,this⟩,this'⟩ : W)
          simp only [Submodule.mkQ_apply]
          have beb : Submodule.submoduleOf ⊥ W = ⊥ := by
              unfold Submodule.submoduleOf
              simp only [Submodule.comap_bot, Submodule.ker_subtype]
          ext z
          simp only [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top,
            Submodule.mem_colon_singleton, Submodule.mem_bot] at *
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, beb]
          simp only [SetLike.mk_smul_mk, Submodule.mem_bot, Submodule.mk_eq_zero]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          constructor
          · intro hz
            have : z • q.out ∈ (N₁.submoduleOf (lift_quot N₁ N₂ W)) := by
              apply (Submodule.Quotient.mk_eq_zero _).1
              simp only [Submodule.Quotient.mk_smul]
              unfold Submodule.Quotient.mk Quotient.mk''
              rwa [Quotient.out_eq]
            exact this
          · intro hz
            simp only [SetLike.mk_smul_mk] at hz
            replace hz : z • q.out ∈ N₁.submoduleOf (lift_quot N₁ N₂ W) := hz
            apply (Submodule.Quotient.mk_eq_zero _).2 at hz
            rw [Submodule.Quotient.mk_smul] at hz
            unfold Submodule.Quotient.mk Quotient.mk'' at hz
            simpa [Quotient.out_eq] using hz
      simp only [this]
    · rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, ⊤), bot_lt_top⟩ =
        _μ R M ⟨(N₁, N₂), hN⟩ := by
        unfold _μ
        simp only
        ext x
        constructor
        · intro hx
          simp only [gt_iff_lt, not_lt, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          use q.out.val
          ext z
          simp only [Submodule.mem_colon_singleton, Submodule.mem_bot] at *
          constructor
          · intro hz
            have : z • q.out.val = (z • q.out).val := rfl
            rw [this]
            replace : z • q.out = 0 := by
              have: ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤).mkQ
                (z • Quotient.out q) = z • q := by
                simp only [map_smul, Submodule.mkQ_apply]
                unfold Submodule.Quotient.mk Quotient.mk''
                rw [Quotient.out_eq]
              rw [hz] at this
              apply (Submodule.Quotient.mk_eq_zero _).1 at this
              have this' : ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤) = ⊥ := by
                unfold Submodule.submoduleOf
                simp only [Submodule.comap_bot, Submodule.ker_subtype]
              simpa only [this'] using this
            rw [this]
            rfl
          · intro hz
            replace hz : z • q.out = 0 := Submodule.coe_eq_zero.mp hz
            have: ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤).mkQ
              (z • Quotient.out q) = z • q := by
              simp only [map_smul, Submodule.mkQ_apply]
              unfold Submodule.Quotient.mk Quotient.mk''
              rw [Quotient.out_eq]
            rw [hz] at this
            simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_zero] using this.symm
        · intro hx
          simp only [gt_iff_lt, not_lt, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : (N₁.submoduleOf N₂).mkQ q.out ∈ (⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := by
            simp only [Submodule.mkQ_apply, Submodule.mem_top]
          use Submodule.Quotient.mk (⟨(N₁.submoduleOf N₂).mkQ q.out, this⟩ :
            ↥(⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)))
          ext z
          simp only [Submodule.nontrivial_iff, Submodule.Quotient.nontrivial_iff, ne_eq,
            Submodule.submoduleOf_eq_top, Submodule.mem_colon_singleton, Submodule.mem_bot,
            Submodule.mkQ_apply, Submodule.Quotient.mk_out] at *
          rw [← Submodule.Quotient.mk_smul]
          rw [Submodule.Quotient.mk_eq_zero]
          have this' : ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤) = ⊥ := by
            unfold Submodule.submoduleOf
            simp only [Submodule.comap_bot, Submodule.ker_subtype]
          rw [this']
          simp only [SetLike.mk_smul_mk, Submodule.mem_bot,
            Submodule.mk_eq_zero]
      simp only [this]
      rfl
  · replace h := h.semistable
    have := quot_ntl hN; have := quot_ntl' hN
    refine {semistable := ?_ }
    intro W hW
    simp only [gt_iff_lt, not_lt] at *
    have : (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)) ≠ ⊥ := by
      by_contra hc
      refine hW ?_
      have : Submodule.comap N₂.subtype ↑W = N₁.submoduleOf N₂ := by
        ext x
        constructor
        · intro hx
          have : (N₁.submoduleOf N₂).mkQ x ∈ Submodule.map (N₁.submoduleOf N₂).mkQ
            (Submodule.comap N₂.subtype ↑W) := by
            exact Submodule.mem_map_of_mem hx
          rw [hc] at this
          simpa only
            [Submodule.mkQ_apply, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] using this
        · intro hx
          exact W.prop.1 hx
      apply Subtype.coe_inj.1
      ext y
      constructor
      · intro hy
        have this' : (⟨y, W.prop.2 hy⟩ : N₂) ∈ Submodule.comap N₂.subtype ↑W := hy
        rwa [this] at this'
      · intro hy
        exact W.prop.1 hy
    specialize h (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)) this
    convert h
    · rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      replace : _μ R M ⟨(↑(⊥: Interval ⟨(N₁, N₂), hN⟩), ↑W), by
        simp only [Subtype.coe_lt_coe, bot_lt_iff_ne_bot, ne_eq, hW, not_false_eq_true]
      ⟩ = _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)
          ⟨(⊥, Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ
            (Submodule.comap (Submodule.subtype N₂) ↑W)),
            Ne.bot_lt' (id (Ne.symm this))⟩ := by
        unfold _μ
        simp only
        ext x
        constructor
        · intro hx
          simp only [Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : (⟨q.out,W.prop.2 q.out.prop⟩ : N₂) ∈
            (Submodule.comap (Submodule.subtype N₂) ↑W) := by
            simp only [Submodule.mem_comap, Submodule.subtype_apply, SetLike.coe_mem]
          have this' : (Submodule.submoduleOf N₁ N₂).mkQ (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩
            : (Submodule.comap (Submodule.subtype N₂) ↑W)).val ∈ Submodule.map
            (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W) := by
            simp only [Submodule.mem_map]
            use (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩ :
              (Submodule.comap (Submodule.subtype N₂) ↑W))
          use Submodule.Quotient.mk ⟨(Submodule.submoduleOf N₁ N₂).mkQ
            (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩ :
              (Submodule.comap (Submodule.subtype N₂) ↑W)).val,this'⟩
          simp only [Submodule.mkQ_apply]
          ext z
          simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot,
            Submodule.mk_eq_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk, Submodule.mem_comap, Submodule.subtype_apply]
          replace : z • q.out.val ∈ N₁ ↔ z • q.out ∈ (N₁.submoduleOf W.val) :=
            { mp := fun h ↦ h, mpr := fun h ↦ h }
          rw [this, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
        · intro hx
          simp only [Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : q.out.val.out ∈ W.val.submoduleOf N₂ := by
            refine Submodule.mem_comap.mpr ?_
            obtain ⟨x, hx₁, hx₂⟩ := Submodule.mem_map.mp q.out.property
            rw [Submodule.mem_comap] at hx₁
            change (Quotient.out q.out.val).val ∈ W.val
            obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul (N₁.submoduleOf N₂).toAddSubgroup x
            change Quotient.out ((N₁.submoduleOf N₂).mkQ x) = x + y.val at hy
            rw [← hx₂, hy]
            change x.val + y.val.val ∈ W.val
            exact Submodule.add_mem _ hx₁ <| W.prop.1 y.property
          use Submodule.Quotient.mk (⟨q.out.val.out,this⟩ : W.val)
          ext z
          simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          replace : z • ⟨q.out.val.out.val, this⟩ ∈ Submodule.submoduleOf N₁ W.val ↔
            z • q.out.val.out ∈ N₁.submoduleOf N₂ := Eq.to_iff rfl
          unfold Bot.bot OrderBot.toBot BoundedOrder.toOrderBot instBoundedOrderInterval
          rw [this, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
          replace : z • q.out = 0 ↔ z • q.out.val = 0 := beq_eq_beq.mp rfl
          rw [← this]
          replace : (z • q).out ∈ (⊥: Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf
            (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ
            (Submodule.comap (Submodule.subtype N₂) ↑W)) ↔ z • q = 0 := by
            rw [← Submodule.Quotient.mk_eq_zero]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
          rw [← this]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot]
          replace : (z • q).out - z • q.out ∈
            (⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf
            (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ
            (Submodule.comap (Submodule.subtype N₂) ↑W)) := by
            rw [← Submodule.Quotient.mk_eq_zero]
            simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq, Quotient.out_eq]
            exact sub_self (z • q)
          unfold Submodule.submoduleOf at this
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot] at this
          constructor
          · intro h
            rw [h] at this
            simpa only [zero_sub, neg_eq_zero] using this
          · intro h
            rw [h] at this
            simpa only [sub_zero] using this
      simp only [this]
    · rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [ Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      replace : _μ R M ⟨(↑(⊥:Interval ⟨(N₁, N₂), hN⟩), ↑(⊤:Interval ⟨(N₁, N₂), hN⟩)), hN⟩ =
        _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, ⊤), bot_lt_top⟩ := by
        unfold _μ
        simp only
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hx
          simp only [ne_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          replace : q ∈ (⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := trivial
          use Submodule.Quotient.mk ⟨q,this⟩
          ext z
          simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype,
            Submodule.mem_bot, Submodule.mk_eq_zero]
        · intro hx
          simp only [ne_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          use Submodule.Quotient.mk q.out.val.out
          ext z
          simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Submodule.Quotient.mk_out]
          replace : z • q.out.val = (z • q.out).val := rfl
          rw [this]
          replace : (z • q.out).val = 0 ↔ z • q.out = 0 := Submodule.coe_eq_zero
          rw [this]
          replace :  z • q = 0 ↔ (z • q).out ∈ Submodule.submoduleOf ⊥ ⊤ := by
            rw [← Submodule.Quotient.mk_eq_zero]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
          rw [this]
          replace : (⊥ :  Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤ = ⊥ := by
            unfold Submodule.submoduleOf
            simp only [Submodule.comap_bot, Submodule.ker_subtype]
          simp only [this, Submodule.mem_bot]
          have this' : (z • q).out - z • q.out ∈
            (⊥ :  Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤ := by
            apply (Submodule.Quotient.mk_eq_zero _).1
            simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
            unfold Submodule.Quotient.mk Quotient.mk''
            simp only [Quotient.out_eq, sub_self]
          simp only [this, Submodule.mem_bot] at this'
          constructor
          · intro h
            rw [h] at this'
            simpa only [zero_sub, neg_eq_zero] using this'
          · intro h
            rw [h] at this'
            simpa only [sub_zero] using this'
      simp only [this]


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
  have := HNFil.piecewise_semistable n hn
  have ntl : Nontrivial (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n)
    (HNFil.filtration (n + 1))) := by
    rw [Submodule.Quotient.nontrivial_iff]
    by_contra hc
    have h' : ∀ x ∈ HNFil.filtration (n + 1), x ∈ HNFil.filtration n := by
      intro x hx
      have : ⟨x,hx⟩ ∈ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)) :=
        hc ▸ Submodule.mem_top
      simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using this
    exact (not_lt_of_ge h') <| HNFil.strict_mono n (n+1) (lt_add_one n) hn
  have ttt : Semistable (μ R (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf
    (HNFil.filtration n) (HNFil.filtration (n + 1)))) := by
    rw [← semistable_res_iff_semistable_quot]
    exact this
  exact { coprimary := rmk4d14₂.mp ttt }


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
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.lt_iff_lt] at this
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
    simp only [pcnp1.unique pcnp1.exists.choose_spec hp1]
  have t'' : (_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1)
    (Nat.lt_add_one n) (Nat.le_of_succ_le hn)⟩).toFinset.min' (μ_nonempty _) =
    {asIdeal := pcn.exists.choose, isPrime := pcn.exists.choose_spec.out.1} := by
    replace := ((_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1)
      (Nat.lt_add_one n) <| le_of_lt hn⟩).toFinset.min'_mem (μ_nonempty _)).out
    apply Set.mem_toFinset.mp at this
    rcases this.out with ⟨p,hp1,hp2⟩
    rw [← hp2]
    simp only [pcn.unique pcn.exists.choose_spec hp1]
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
        have := a.piecewise_coprimary i hi
        have ntl : Nontrivial (↥(a.filtration (i + 1)) ⧸
          Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1))) := by
          rw [Submodule.Quotient.nontrivial_iff]
          by_contra hc
          have h' : ∀ x ∈ a.filtration (i + 1), x ∈ a.filtration i := by
            intro x hx
            have : ⟨x,hx⟩ ∈ Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1)) :=
              hc ▸ Submodule.mem_top
            simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at this
            exact this
          exact (not_lt_of_ge h') <| a.strict_mono i (i+1) (lt_add_one i) hi
        replace this := this.coprimary
        rwa [← rmk4d14₂,← semistable_res_iff_semistable_quot] at this
      · intro i hi
        have := a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)
        repeat rw [prop3d12]
        simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
          OrderEmbedding.le_iff_le, not_le, gt_iff_lt]
        apply S₀_order'.1
        convert a.strict_mono_associated_prime i hi
        · replace := (_μ R M ⟨(a.filtration (i + 1), a.filtration (i + 2)), a.strict_mono (i+1)
            (i+2) (Nat.lt_add_one (i + 1)) hi⟩).toFinset.min'_mem (μ_nonempty _)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          simp only [(a.piecewise_coprimary (i+1) hi).coprimary.unique
            ((a.piecewise_coprimary (i+1) hi).coprimary.exists.choose_spec) hp1]
        · replace := (_μ R M ⟨(a.filtration i, a.filtration (i + 1)), a.strict_mono i
            (i+1) (Nat.lt_add_one i) (Nat.le_of_succ_le hi)⟩).toFinset.min'_mem (μ_nonempty _)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          simp only [(a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.unique
            ((a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.exists.choose_spec) hp1]
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
