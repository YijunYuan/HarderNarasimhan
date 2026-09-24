/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Coprimary.AssociatedPrimes
public import HarderNarasimhan.Coprimary.Defs
public import HarderNarasimhan.PayoffFunction.Convex
public import HarderNarasimhan.PayoffFunction.Semistable.Defs
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Semistability of the coprimary payoff function

Let `M` be a finitely generated module over a commutative Noetherian ring. This file
computes the value of the coprimary payoff function when player A moves first. For `M ≠ 0`,
this payoff function is semistable precisely when `M` is coprimary.

All comparisons of prime ideals use the fixed linear extension of the prime spectrum.
In particular, the least associated prime below refers to this linear order.

## Main results

* `HarderNarasimhan.Coprimary.A_payoff`: the value when A moves first on `N₁ < N₂` is the
  singleton containing the least associated prime of `N₂ ⧸ N₁`.
* `HarderNarasimhan.Coprimary.isSemistable_iff_existsUnique_associatedPrime`: for `M ≠ 0`,
  semistability is equivalent to having exactly one associated prime.
* `HarderNarasimhan.Coprimary.isSemistable_restrict_iff_quotient`: semistability of the restriction
  to an interval is equivalent to semistability of the payoff function of its subquotient.

The coprimary payoff function is convex and satisfies the descending chain condition
`HarderNarasimhan.PayoffFunction.ADCC`. These instances allow the existence theorem for
Harder–Narasimhan filtrations to be applied in `HarderNarasimhan/Coprimary/Filtration.lean`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace Coprimary

section Subquotient

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The subquotient of a strict inclusion of submodules is nontrivial. -/
lemma nontrivial_quotient_of_lt {N₁ N₂ : Submodule R M} (hN : N₁ < N₂) :
    Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
  exact hN.not_ge

/-- If `N₁ < u ≤ N₃`, every associated prime of `u ⧸ N₁` is an associated prime of
`N₃ ⧸ N₁`. -/
lemma subquotientAssociatedPrimes_mono_right {N₁ u N₃ : Submodule R M}
    (h₁ : N₁ < u) (h₂ : u ≤ N₃) :
    subquotientAssociatedPrimes ⟨N₁, u, h₁⟩ ⊆
      subquotientAssociatedPrimes ⟨N₁, N₃, h₁.trans_le h₂⟩ :=
  fun _ hi ↦ associatedPrimes_subset_of_submoduleOf_le N₁ u N₃ h₂ hi

/-- The preimage of a submodule of `N₂ / (N₂ ∩ N₁)` under the quotient map, viewed as a
submodule of `M`. -/
private def liftQuot (N₁ N₂ : Submodule R M) (x : Submodule R (N₂ ⧸ N₁.submoduleOf N₂)) :
    Submodule R M :=
  Submodule.map N₂.subtype (Submodule.comap (N₁.submoduleOf N₂).mkQ x)

/-- If `N₁ ≤ N₂`, then `N₁ ≤ liftQuot N₁ N₂ x ≤ N₂`. -/
private lemma liftQuot_middle (N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
    (x : Submodule R (N₂ ⧸ N₁.submoduleOf N₂)) :
    N₁ ≤ liftQuot N₁ N₂ x ∧ liftQuot N₁ N₂ x ≤ N₂ := by
  refine ⟨?_, Submodule.map_subtype_le _ _⟩
  refine le_trans ?_ (Submodule.map_mono (Submodule.le_comap_mkQ _ _))
  change N₁ ≤ Submodule.map N₂.subtype (N₁.submoduleOf N₂)
  rw [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right.2 hN]

/-- The lift of a nonzero submodule of `N₂ / (N₂ ∩ N₁)` differs from `N₁`. -/
private lemma liftQuot_ne_left (N₁ N₂ : Submodule R M)
    (x : Submodule R (N₂ ⧸ N₁.submoduleOf N₂)) (hx : x ≠ ⊥) : liftQuot N₁ N₂ x ≠ N₁ := by
  intro hc
  refine hx ?_
  rw [← (Submodule.comapMkQRelIso (N₁.submoduleOf N₂)).injective.eq_iff]
  apply Subtype.ext
  change Submodule.comap (N₁.submoduleOf N₂).mkQ x = LinearMap.ker _
  rw [Submodule.ker_mkQ]
  refine le_antisymm ?_ (Submodule.le_comap_mkQ _ _)
  intro a ha
  simpa [← hc] using ⟨a, ha, rfl⟩

/-- The isomorphism between `(N₂ / (N₂ ∩ N₁)) / X` and the quotient of `N₂` by the
preimage of `X`, given by the third isomorphism theorem. -/
private noncomputable def quotLiftQuotEquiv (N₁ N₂ : Submodule R M)
    (X : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)) :
    (↥N₂ ⧸ (liftQuot N₁ N₂ X).submoduleOf N₂) ≃ₗ[R] ((↥N₂ ⧸ N₁.submoduleOf N₂) ⧸ X) :=
  (Submodule.quotEquivOfEq _ _ (Submodule.comap_map_eq_of_injective N₂.subtype_injective _)).trans
    (Submodule.map_comap_eq_self (Submodule.range_mkQ (N₁.submoduleOf N₂) ▸ le_top (a := X)) ▸
      (Submodule.quotientQuotientEquivQuotient (N₁.submoduleOf N₂) _
        (Submodule.le_comap_mkQ _ _)).symm)

/-- For `N₁ ≤ W ≤ N₂`, the canonical isomorphism from `W ⧸ N₁` to the image of `W` in
`N₂ ⧸ N₁`. -/
private noncomputable def quotEquivMapComap {N₁ N₂ W : Submodule R M}
    (_ : N₁ ≤ W) (h₂ : W ≤ N₂) :
    (↥W ⧸ N₁.submoduleOf W) ≃ₗ[R]
      Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) := by
  let i : W →ₗ[R] N₂ := Submodule.inclusion h₂
  let f : W →ₗ[R] (↥N₂ ⧸ N₁.submoduleOf N₂) := (N₁.submoduleOf N₂).mkQ.comp i
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

/-- The image of `W` in `N₂ ⧸ N₁` is nonzero when `N₁ < W ≤ N₂`. -/
lemma map_comap_ne_bot {N₁ N₂ W : Submodule R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂)
    (h₃ : W ≠ N₁) :
    Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) ≠ ⊥ := by
  intro hbot
  refine h₃ <| le_antisymm ?_ h₁
  intro x hx
  have hx_image : (N₁.submoduleOf N₂).mkQ ⟨x, h₂ hx⟩ ∈
      Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) :=
    Submodule.mem_map_of_mem hx
  change (⟨x, h₂ hx⟩ : N₂) ∈ N₁.submoduleOf N₂
  simpa [hbot, Submodule.Quotient.mk_eq_zero] using hx_image

/-- Associated primes agree under the submodule correspondence for a quotient. -/
private lemma subquotientAssociatedPrimes_eq_quotient {N₁ N₂ W : Submodule R M}
    (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂) (h₃ : W ≠ N₁) :
    subquotientAssociatedPrimes ⟨N₁, W, h₁.lt_of_ne' h₃⟩ =
      subquotientAssociatedPrimes (M := ↥N₂ ⧸ N₁.submoduleOf N₂)
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let X := Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)
  have hX : (⊥ : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)).submoduleOf X = ⊥ :=
    Submodule.ker_subtype X
  ext x
  simp only [mem_subquotientAssociatedPrimes]
  constructor <;> intro hp
  · rw [LinearEquiv.AssociatedPrimes.eq
      ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
    simpa [X, hX] using hp
  · rw [← LinearEquiv.AssociatedPrimes.eq
      ((quotEquivMapComap h₁ h₂).trans (Submodule.quotEquivOfEqBot _ hX).symm)] at hp
    simpa [X, hX] using hp

end Subquotient

section Payoff

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The subquotient of a strict inclusion has an associated prime. -/
lemma subquotientAssociatedPrimes_nonempty (I : StrictIntvl (Submodule R M)) :
    (subquotientAssociatedPrimes I).toFinset.Nonempty := by
  simp only [Set.toFinset_nonempty]
  let : Nontrivial (↥I.right ⧸ I.left.submoduleOf I.right) := nontrivial_quotient_of_lt I.lt
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R (↥I.right ⧸ I.left.submoduleOf I.right)
  exact ⟨⟨q, hq.out.1⟩, hq⟩

/-- The least associated prime of a subquotient belongs to its set of associated primes. -/
lemma min'_mem_subquotientAssociatedPrimes (I : StrictIntvl (Submodule R M)) :
    (subquotientAssociatedPrimes I).toFinset.min' (subquotientAssociatedPrimes_nonempty I) ∈
      subquotientAssociatedPrimes I :=
  (Set.mem_toFinset (s := subquotientAssociatedPrimes I)).mp <|
    (subquotientAssociatedPrimes I).toFinset.min'_mem (subquotientAssociatedPrimes_nonempty I)

/-- If a subquotient has exactly one associated prime, that prime is the least element of
its set of associated primes in the linear extension. -/
lemma toLinearExtension_eq_min' (I : StrictIntvl (Submodule R M))
    (hu : ∃! p, p ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right))
    {p : PrimeSpectrum R}
    (hp : p.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)) :
    toLinearExtension p =
      (subquotientAssociatedPrimes I).toFinset.min' (subquotientAssociatedPrimes_nonempty I) :=
  PrimeSpectrum.ext (hu.unique hp (min'_mem_subquotientAssociatedPrimes I))

/-- The coprimary payoff function is unchanged by taking the supremum over subintervals
with the same left endpoint. -/
lemma max_payoff : (payoff R M).max = payoff R M := by
  refine PayoffFunction.ext fun I ↦
    le_antisymm (PayoffFunction.max_le fun u hu ↦ ?_) PayoffFunction.apply_le_max
  simp only [payoff_apply]
  exact DedekindCut.principal_le_principal.mpr <| Finset.Colex.toColex_le_toColex_of_subset <|
    Set.toFinset_subset_toFinset.mpr <| subquotientAssociatedPrimes_mono_right hu.1 hu.2

/-- The coprimary payoff function is convex. -/
instance [Nontrivial M] : (payoff R M).IsConvexOn ⊤ := by
  refine { le := fun x y _ _ hxy ↦ ?_ }
  simp only [payoff_apply]
  refine DedekindCut.principal_le_principal.mpr <| Finset.Colex.toColex_le_toColex_of_subset <|
    Set.toFinset_subset_toFinset.mpr ?_
  intro w hw
  rw [mem_subquotientAssociatedPrimes, AssociatedPrimes.mem_iff] at hw ⊢
  exact (LinearEquiv.isAssociatedPrime_iff (LinearMap.quotientInfEquivSupQuotient x y)).1 hw

/-- The least associated prime of `I.right ⧸ I.left` is a lower bound, in the linear
extension, for the associated primes of `I.right ⧸ N''` when `I.left ≤ N'' ≤ I.right`. -/
private lemma min'_le_toLinearExtension (I : StrictIntvl (Submodule R M))
    (N'' : Submodule R M) (ha1 : N'' ∈ I) :
    ∀ p : PrimeSpectrum R,
      p.asIdeal ∈ associatedPrimes R (I.right ⧸ N''.submoduleOf I.right) →
      (subquotientAssociatedPrimes I).toFinset.min' (subquotientAssociatedPrimes_nonempty I) ≤
        toLinearExtension p := by
  intro p hp
  have hle : I.left.submoduleOf I.right ≤ N''.submoduleOf I.right :=
    Submodule.comap_mono ha1.1
  have hann : Module.annihilator R (I.right ⧸ I.left.submoduleOf I.right) ≤ p.asIdeal := by
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
  exact le_trans ((subquotientAssociatedPrimes I).toFinset.min'_le
    (toLinearExtension ⟨r, hr.1.1⟩) <|
    Set.mem_toFinset.mpr <|
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hr) <|
    toLinearExtension.monotone' (hrq : (⟨r, hr.1.1⟩ : PrimeSpectrum R) ≤ p)

/-- For `I.left ≤ N'' < I.right`, the singleton containing the least associated prime of
`I.right ⧸ I.left` is a lower bound in colexicographic order for the finite set of associated
primes of `I.right ⧸ N''`. -/
private lemma singleton_min'_le (I : StrictIntvl (Submodule R M))
    (N'' : Submodule R M) (ha1 : N'' ∈ I) (ha2 : N'' ≠ I.right) :
    toColex {(subquotientAssociatedPrimes I).toFinset.min'
        (subquotientAssociatedPrimes_nonempty I)} ≤
      toColex (subquotientAssociatedPrimes ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset := by
  let J : StrictIntvl (Submodule R M) := ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩
  calc
    _ ≤ toColex {(subquotientAssociatedPrimes J).toFinset.min'
        (subquotientAssociatedPrimes_nonempty J)} := by
      rw [Finset.Colex.singleton_le_singleton]
      exact min'_le_toLinearExtension I N'' ha1 _ (min'_mem_subquotientAssociatedPrimes J)
    _ ≤ toColex (subquotientAssociatedPrimes J).toFinset :=
      Finset.Colex.toColex_le_toColex_of_subset <| Finset.singleton_subset_iff.mpr <|
        (subquotientAssociatedPrimes J).toFinset.min'_mem (subquotientAssociatedPrimes_nonempty J)

/-- The kernel of the localization map of `I.right ⧸ I.left` at its least associated
prime in the linear extension. -/
private noncomputable abbrev locKer (I : StrictIntvl (Submodule R M)) :
    Submodule R (↥I.right ⧸ I.left.submoduleOf I.right) :=
  LinearMap.ker (LocalizedModule.mkLinearMap
    (((subquotientAssociatedPrimes I).toFinset.min'
      (subquotientAssociatedPrimes_nonempty I)).asIdeal.primeCompl)
    (↥I.right ⧸ I.left.submoduleOf I.right))

/-- Quotienting by the lifted localization kernel gives a coprimary module whose associated
prime is the least associated prime of `I.right ⧸ I.left`. -/
private lemma associatedPrimes_quot_liftQuot_locKer (I : StrictIntvl (Submodule R M)) :
    associatedPrimes R
        (↥I.right ⧸ (liftQuot I.left I.right (locKer I)).submoduleOf I.right) =
      {((subquotientAssociatedPrimes I).toFinset.min'
        (subquotientAssociatedPrimes_nonempty I)).asIdeal} := by
  rw [LinearEquiv.AssociatedPrimes.eq (quotLiftQuotEquiv I.left I.right (locKer I)),
    associatedPrimes_quot_ker_mkLinearMap]
  ext q
  constructor
  · rintro ⟨hq, hdisj⟩
    simp only [Set.mem_singleton_iff]
    apply congrArg PrimeSpectrum.asIdeal (show toLinearExtension ⟨q, hq.out.1⟩ = _ from ?_)
    apply le_antisymm
    · exact toLinearExtension.monotone' (Set.sdiff_eq_empty.mp hdisj)
    · exact (subquotientAssociatedPrimes I).toFinset.min'_le _ (Set.mem_toFinset.mpr hq)
  · rintro rfl
    refine ⟨min'_mem_subquotientAssociatedPrimes I, ?_⟩
    unfold Ideal.primeCompl
    simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.inter_compl_self]

/-- The value of the coprimary payoff function on `I` when player A moves first is the singleton
containing the least associated prime of `I.right ⧸ I.left` in the fixed linear extension
of the prime spectrum, embedded in the Dedekind–MacNeille completion. -/
lemma A_payoff (I : StrictIntvl (Submodule R M)) :
    (payoff R M).A I =
      .principal (toColex {(subquotientAssociatedPrimes I).toFinset.min'
        (subquotientAssociatedPrimes_nonempty I)}) := by
  apply le_antisymm
  · -- The lifted localization kernel realizes the upper bound.
    obtain ⟨hleft, hright⟩ := liftQuot_middle I.left I.right I.lt.le (locKer I)
    have hne : liftQuot I.left I.right (locKer I) ≠ I.right := by
      intro hc
      let : Subsingleton (↥I.right ⧸ (liftQuot I.left I.right (locKer I)).submoduleOf I.right) :=
        Submodule.Quotient.subsingleton_iff.mpr (Submodule.submoduleOf_eq_top.mpr hc.ge)
      exact Set.singleton_ne_empty _
        ((associatedPrimes_quot_liftQuot_locKer I).symm.trans
          associatedPrimes.eq_empty_of_subsingleton)
    refine (PayoffFunction.A_le (I := I) ⟨hleft, lt_of_le_of_ne hright hne⟩).trans_eq ?_
    rw [max_payoff, payoff_apply, DedekindCut.principal_inj, toColex_inj]
    refine (Set.toFinset_congr ?_).trans (Set.toFinset_singleton _)
    ext w
    rw [mem_subquotientAssociatedPrimes, associatedPrimes_quot_liftQuot_locKer I,
      Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ PrimeSpectrum.ext h, fun h ↦ congrArg PrimeSpectrum.asIdeal h⟩
  · -- Every legal first move satisfies the singleton lower bound.
    apply PayoffFunction.le_A
    intro a ha
    rw [max_payoff, payoff_apply]
    exact DedekindCut.principal_le_principal.mpr <| singleton_min'_le I a ⟨ha.1, ha.2.le⟩ ha.2.ne

/-- The coprimary payoff function satisfies the descending chain condition
`HarderNarasimhan.PayoffFunction.ADCC`. -/
instance : (payoff R M).ADCC where
  dcc := by
    intro N x hx1 hx2
    by_contra hc
    simp only [not_exists, A_payoff, DedekindCut.principal_lt_principal,
      Finset.Colex.singleton_lt_singleton, not_not] at hc
    -- The strictly increasing minima would give infinitely many primes in one finite set.
    refine (associatedPrimes.finite R ((↥(x 0) ⧸ N.submoduleOf (x 0)))).not_infinite ?_
    refine Set.infinite_of_injective_forall_mem
      (f := fun i ↦ ((subquotientAssociatedPrimes ⟨N, x i, hx1 i⟩).toFinset.min'
        (subquotientAssociatedPrimes_nonempty _)).asIdeal) ?_ ?_
    · intro a b hab
      exact (strictMono_nat_of_lt_succ hc).injective (PrimeSpectrum.ext hab)
    · intro i
      exact associatedPrimes_subset_of_submoduleOf_le N (x i) (x 0) (hx2.antitone i.zero_le)
        (min'_mem_subquotientAssociatedPrimes ⟨N, x i, hx1 i⟩)

/-- Semistability of the coprimary payoff function is equivalent to constancy of the value
when A moves first on the intervals `(⊥, N)`. This value is the singleton containing the
least associated prime of `M` in the linear extension. -/
theorem isSemistable_iff_A_const [Nontrivial M] :
    (payoff R M).IsSemistable ↔ ∀ N : Submodule R M, (hN : ⊥ < N) →
      (payoff R M).A ⟨⊥, N, hN⟩ =
        .principal (toColex {(subquotientAssociatedPrimes
          (⊤ : StrictIntvl (Submodule R M))).toFinset.min'
          (subquotientAssociatedPrimes_nonempty ⊤)}) := by
  constructor
  · intro hst N hN
    have hst' : ¬ (payoff R M).A ⊤ < (payoff R M).A ⟨⊥, N, hN⟩ := hst.not_lt N hN
    rw [A_payoff ⟨⊥, N, hN⟩, A_payoff (⊤ : StrictIntvl (Submodule R M)),
      DedekindCut.principal_lt_principal, Finset.Colex.singleton_lt_singleton, not_lt] at hst'
    rw [A_payoff ⟨⊥, N, hN⟩]
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
    exact eq_of_le_of_ge hst' <| Finset.min'_subset (subquotientAssociatedPrimes_nonempty _) <|
      Set.toFinset_subset_toFinset.mpr <| subquotientAssociatedPrimes_mono_right hN le_top
  · refine fun h ↦ { not_lt := fun N hN ↦ ?_ }
    rw [h N hN, A_payoff (⊤ : StrictIntvl (Submodule R M))]
    exact lt_irrefl _

/-- The coprimary payoff function of a nonzero finitely generated module over a Noetherian
ring is semistable if and only if the module has exactly one associated prime. -/
theorem isSemistable_iff_existsUnique_associatedPrime [Nontrivial M] :
    (payoff R M).IsSemistable ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [isSemistable_iff_A_const]
  let p0 := (subquotientAssociatedPrimes (⊤ : StrictIntvl (Submodule R M))).toFinset.min'
    (subquotientAssociatedPrimes_nonempty ⊤)
  have hbot (N : Submodule R M) : (⊥ : Submodule R M).submoduleOf N = ⊥ :=
    Submodule.ker_subtype N
  let eTop : (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).submoduleOf ⊤) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ (hbot ⊤)).trans Submodule.topEquiv
  have hp0 : p0.asIdeal ∈ associatedPrimes R M := by
    simpa [LinearEquiv.AssociatedPrimes.eq eTop] using
      min'_mem_subquotientAssociatedPrimes (⊤ : StrictIntvl (Submodule R M))
  constructor
  · refine fun hs ↦ ⟨p0.asIdeal, hp0, fun J hJ ↦ ?_⟩
    -- A vector with annihilator `J` generates a submodule whose only associated prime is `J`.
    obtain ⟨hJp, t, ht⟩ := (isAssociatedPrime_iff (R := R) (M := M)).1 <|
      (AssociatedPrimes.mem_iff (R := R) (M := M)).1 hJ
    have hN : ⊥ < (R ∙ t : Submodule R M) := by
      rw [bot_lt_iff_ne_bot, ne_eq, Submodule.span_singleton_eq_bot]
      exact fun ht0 ↦ hJp.ne_top (by rw [ht, ht0, Submodule.colon_singleton_zero])
    have hassN : associatedPrimes R ↥(R ∙ t : Submodule R M) = {J} := by
      have htors : Ideal.torsionOf R M t = J := by
        ext a
        rw [Ideal.mem_torsionOf_iff, ht, Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [← LinearEquiv.AssociatedPrimes.eq (Ideal.quotTorsionOfEquivSpanSingleton R M t), htors,
        associatedPrimes.eq_singleton_of_isPrimary hJp.isPrimary, hJp.radical]
    -- Constancy of the value when A moves first identifies that prime with the global minimum.
    have hmin : (subquotientAssociatedPrimes ⟨⊥, R ∙ t, hN⟩).toFinset.min'
        (subquotientAssociatedPrimes_nonempty _) = ⟨J, hJp⟩ := by
      apply PrimeSpectrum.ext
      apply Set.mem_singleton_iff.mp
      rw [← hassN]
      simpa [LinearEquiv.AssociatedPrimes.eq (Submodule.quotEquivOfEqBot _ (hbot (R ∙ t)))] using
        min'_mem_subquotientAssociatedPrimes (⟨⊥, R ∙ t, hN⟩ : StrictIntvl (Submodule R M))
    have hs' := hs (R ∙ t) hN
    rw [A_payoff ⟨⊥, R ∙ t, hN⟩] at hs'
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj] at hs'
    exact congrArg PrimeSpectrum.asIdeal (hmin.symm.trans hs')
  · rintro ⟨p, hp, hp_unique⟩ N hN
    rw [A_payoff ⟨⊥, N, hN⟩]
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
    have hq : ((subquotientAssociatedPrimes ⟨⊥, N, hN⟩).toFinset.min'
        (subquotientAssociatedPrimes_nonempty _)).asIdeal ∈ associatedPrimes R M := by
      simpa [LinearEquiv.AssociatedPrimes.eq eTop] using
        subquotientAssociatedPrimes_mono_right hN le_top
          (min'_mem_subquotientAssociatedPrimes (⟨⊥, N, hN⟩ : StrictIntvl (Submodule R M)))
    exact PrimeSpectrum.ext ((hp_unique _ hq).trans (hp_unique _ hp0).symm)

/-- For `N₁ < W ≤ N₂`, the value when A moves first on `(N₁, W)` equals the corresponding
value on `(⊥, W ⧸ N₁)` in the submodule lattice of `N₂ ⧸ N₁`. -/
lemma A_restrict_eq_quotient {N₁ N₂ W : Submodule R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂)
    (h₃ : W ≠ N₁) :
    (payoff R M).A ⟨N₁, W, h₁.lt_of_ne' h₃⟩ =
      (payoff R (↥N₂ ⧸ N₁.submoduleOf N₂)).A
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  rw [A_payoff, A_payoff]
  simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
  simp [subquotientAssociatedPrimes_eq_quotient h₁ h₂ h₃]

/-- The coprimary payoff function restricted to `(N₁, N₂)` is semistable if and only if the
coprimary payoff function of `N₂ ⧸ N₁` is semistable. -/
lemma isSemistable_restrict_iff_quotient (N₁ N₂ : Submodule R M) (hN : N₁ < N₂) :
    ((payoff R M).restrict ⟨N₁, N₂, hN⟩).IsSemistable ↔
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
      (payoff R (↥N₂ ⧸ N₁.submoduleOf N₂)).IsSemistable := by
  refine ⟨?_, ?_⟩
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
    refine { not_lt := fun X hX ↦ ?_ }
    -- Lift the proposed destabilizing submodule to the original interval.
    have hmid := liftQuot_middle N₁ N₂ hN.le X
    have hneq : liftQuot N₁ N₂ X ≠ N₁ := liftQuot_ne_left N₁ N₂ X hX.ne'
    have hres := h.not_lt ⟨liftQuot N₁ N₂ X, hmid⟩
      (bot_lt_iff_ne_bot.2 fun hc ↦ hneq (Subtype.coe_inj.mpr hc))
    simp only [PayoffFunction.A_restrict_apply] at hres
    change ¬ (payoff R M).A ⟨N₁, N₂, hN⟩ <
      (payoff R M).A ⟨N₁, liftQuot N₁ N₂ X, hmid.1.lt_of_ne' hneq⟩ at hres
    rw [A_restrict_eq_quotient hmid.1 hmid.2 hneq,
      A_restrict_eq_quotient hN.le le_rfl hN.ne'] at hres
    simpa [liftQuot, Submodule.comap_map_eq, Submodule.ker_subtype,
      Submodule.map_comap_eq_self, Submodule.range_mkQ] using hres
  · let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
    refine fun h ↦ { not_lt := fun W hW ↦ ?_ }
    have hW' : W.val ≠ N₁ := fun hEq ↦ hW.ne' (Subtype.ext hEq)
    -- Pass the interval submodule to its image in the quotient.
    simp only [PayoffFunction.A_restrict_apply]
    change ¬ (payoff R M).A ⟨N₁, N₂, hN⟩ <
      (payoff R M).A ⟨N₁, W.val, W.prop.1.lt_of_ne' hW'⟩
    rw [A_restrict_eq_quotient W.prop.1 W.prop.2 hW',
      A_restrict_eq_quotient hN.le le_rfl hN.ne']
    simpa [Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ] using
      h.not_lt (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W.val))
        (bot_lt_iff_ne_bot.2 <| map_comap_ne_bot W.prop.1 W.prop.2 hW')

end Payoff

end Coprimary

end HarderNarasimhan
