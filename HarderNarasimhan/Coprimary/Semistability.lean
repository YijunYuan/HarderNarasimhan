/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Algebra.Module.Torsion.Basic
import HarderNarasimhan.Coprimary.AssociatedPrimes
import HarderNarasimhan.Coprimary.Defs
import HarderNarasimhan.PayoffFunction.Convex
import HarderNarasimhan.PayoffFunction.Semistable.Defs

/-!
# Semistability of the coprimary payoff function

This file establishes the game-theoretic properties of the coprimary payoff function
`Coprimary.payoff R M` that feed the general Harder–Narasimhan machinery, and identifies its
semistability with the classical coprimarity condition.

The key computation is `Coprimary.A_payoff`: the first-player value of the game on an
interval `(N₁, N₂)` of submodules is the singleton containing the *minimal* associated prime
of `N₂ ⧸ N₁` (in the fixed linear extension of the prime spectrum).  The optimal first move
is exhibited by the kernel of the localization of `N₂ ⧸ N₁` at that minimal prime, whose
associated primes are computed by `associatedPrimes_quot_ker_mkLinearMap` from
`HarderNarasimhan.Coprimary.AssociatedPrimes`.

From this computation the standing hypotheses of the general theory follow: convexity
(the `IsConvexOn ⊤` instance) and the descending chain condition (the `ADCC` instance, by
finiteness of the associated primes of a fixed module over a Noetherian ring).  Moreover
semistability of `Coprimary.payoff R M` is equivalent to `M` having a unique associated
prime (`Coprimary.isSemistable_iff_existsUnique_associatedPrime`), i.e. to `M` being
coprimary.

Finally, the file provides the translation between the game restricted to an interval
`(N₁, N₂)` of submodules of `M` and the game on the submodule lattice of the subquotient
`N₂ ⧸ N₁` (`Coprimary.A_restrict_eq_quotient` and
`Coprimary.isSemistable_restrict_iff_quotient`); this is how "the subquotients of a
Harder–Narasimhan filtration are coprimary" is extracted in
`HarderNarasimhan.Coprimary.Filtration`.

## Main results

* `Coprimary.A_payoff` : the first-player value is the singleton on the minimal associated
  prime of the subquotient.  This is Proposition 3.12 of [ChenJeannin].
* `Coprimary.isSemistable_iff_A_const`, `Coprimary.isSemistable_iff_existsUnique_associatedPrime` :
  semistability of the coprimary payoff function is equivalent to constancy of the
  first-player value on initial segments, and to `M` having exactly one associated prime.
  These are the two nontrivial equivalences of Remark 3.14 of [ChenJeannin].
* `Coprimary.isSemistable_restrict_iff_quotient` : semistability of the restriction to an
  interval of submodules is semistability of the coprimary payoff function of the
  subquotient.
* The `IsConvexOn ⊤` and `ADCC` instances for `Coprimary.payoff R M` (Propositions 3.11 and
  3.13 of [ChenJeannin]).

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

namespace Coprimary

section Subquotient

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The subquotient of a strict inclusion of submodules is nontrivial. -/
lemma nontrivial_quotient_of_lt {N₁ N₂ : Submodule R M} (hN : N₁ < N₂) :
    Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.submoduleOf_eq_top]
  exact hN.not_ge

/-- Monotonicity of `Coprimary.associatedPrimes` in the right endpoint: if `N₁ < u ≤ N₃`, every
associated prime of `u ⧸ N₁` is an associated prime of `N₃ ⧸ N₁`. -/
lemma associatedPrimes_mono_right {N₁ u N₃ : Submodule R M} (h₁ : N₁ < u) (h₂ : u ≤ N₃) :
    associatedPrimes ⟨N₁, u, h₁⟩ ⊆ associatedPrimes ⟨N₁, N₃, h₁.trans_le h₂⟩ :=
  fun _ hi ↦ associatedPrimes_subset_of_submoduleOf_le N₁ u N₃ h₂ hi

/-- Lift a submodule of a subquotient back to a submodule of the ambient module: for
`x ≤ N₂ ⧸ N₁`, `liftQuot N₁ N₂ x` is the preimage of `x` under the quotient map
`N₂ → N₂ ⧸ N₁`, viewed inside `M` via the inclusion `N₂ ↪ M`. -/
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

/-- If `x ≠ ⊥` as a submodule of the subquotient `N₂ ⧸ N₁`, then `liftQuot N₁ N₂ x ≠ N₁`. -/
private lemma liftQuot_ne_left (N₁ N₂ : Submodule R M)
    (x : Submodule R (N₂ ⧸ N₁.submoduleOf N₂)) (hx : x ≠ ⊥) : liftQuot N₁ N₂ x ≠ N₁ := by
  intro hc
  refine hx ?_
  have h_comap : Submodule.comap (N₁.submoduleOf N₂).mkQ x = N₁.submoduleOf N₂ := by
    refine le_antisymm ?_ (Submodule.le_comap_mkQ _ _)
    intro a ha
    have ha' : a.val ∈ liftQuot N₁ N₂ x := ⟨a, ha, rfl⟩
    rwa [hc] at ha'
  rw [← (Submodule.comapMkQRelIso (N₁.submoduleOf N₂)).injective.eq_iff]
  exact Subtype.ext (h_comap.trans (Submodule.ker_mkQ _).symm)

/-- Third isomorphism theorem for lifted submodules: the quotient of `N₂` by the lift of
`X ≤ N₂ ⧸ N₁` is canonically the quotient `(N₂ ⧸ N₁) ⧸ X`. -/
private noncomputable def quotLiftQuotEquiv (N₁ N₂ : Submodule R M)
    (X : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)) :
    (↥N₂ ⧸ (liftQuot N₁ N₂ X).submoduleOf N₂) ≃ₗ[R] ((↥N₂ ⧸ N₁.submoduleOf N₂) ⧸ X) :=
  (Submodule.quotEquivOfEq _ _ (Submodule.comap_map_eq_of_injective N₂.subtype_injective _)).trans
    (Submodule.map_comap_eq_self (Submodule.range_mkQ (N₁.submoduleOf N₂) ▸ le_top (a := X)) ▸
      (Submodule.quotientQuotientEquivQuotient (N₁.submoduleOf N₂) _
        (Submodule.le_comap_mkQ _ _)).symm)

/-- Subquotients on an interval identify with the corresponding submodules of the quotient
module: for `N₁ ≤ W ≤ N₂`, the module `W ⧸ N₁` is the image of `W` in `N₂ ⧸ N₁`. -/
private noncomputable def quotEquivMapComap {N₁ N₂ W : Submodule R M}
    (_ : N₁ ≤ W) (h₂ : W ≤ N₂) :
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

/-- The image in `N₂ ⧸ N₁` of a submodule `W` with `N₁ ≤ W ≤ N₂` and `W ≠ N₁` is nonzero. -/
private lemma map_comap_ne_bot {N₁ N₂ W : Submodule R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂)
    (h₃ : W ≠ N₁) :
    Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W) ≠ ⊥ := by
  intro hbot
  refine h₃ <| le_antisymm ?_ h₁
  have hle : Submodule.comap N₂.subtype W ≤ N₁.submoduleOf N₂ := fun y hy => by
    have : y ∈ Submodule.comap (N₁.submoduleOf N₂).mkQ ⊥ := hbot ▸ Submodule.mem_map_of_mem hy
    simpa [Submodule.comap_bot, Submodule.ker_mkQ] using this
  intro x hx
  exact hle (show (⟨x, h₂ hx⟩ : N₂) ∈ Submodule.comap N₂.subtype W from hx)

/-- `Coprimary.associatedPrimes` agrees with its quotient-lattice version under the submodule
correspondence. -/
private lemma associatedPrimes_eq_quotient {N₁ N₂ W : Submodule R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂)
    (h₃ : W ≠ N₁) :
    associatedPrimes ⟨N₁, W, lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      associatedPrimes (M := ↥N₂ ⧸ N₁.submoduleOf N₂)
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  let X := Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)
  have hX : (⊥ : Submodule R (↥N₂ ⧸ N₁.submoduleOf N₂)).submoduleOf X = ⊥ :=
    Submodule.ker_subtype X
  ext x
  simp only [mem_associatedPrimes]
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

/-- For a strict inclusion `N₁ < N₂`, the subquotient `N₂ ⧸ N₁` is nontrivial, hence has an
associated prime: the finset of associated primes of any interval is nonempty. -/
lemma associatedPrimes_nonempty (I : StrictIntvl (Submodule R M)) :
    (associatedPrimes I).toFinset.Nonempty := by
  simp only [Set.toFinset_nonempty]
  have : Nontrivial (↥I.right ⧸ I.left.submoduleOf I.right) := nontrivial_quotient_of_lt I.lt
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R (↥I.right ⧸ I.left.submoduleOf I.right)
  exact ⟨⟨q, hq.out.1⟩, hq⟩

/-- The minimal element of the associated primes of an interval is itself an associated
prime of the subquotient. -/
lemma min'_mem_associatedPrimes (I : StrictIntvl (Submodule R M)) :
    (associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I) ∈ associatedPrimes I :=
  (Set.mem_toFinset (s := associatedPrimes I)).mp <|
    (associatedPrimes I).toFinset.min'_mem (associatedPrimes_nonempty I)

/-- If the subquotient of `I` has a unique associated prime, every associated prime computes
the minimal element of `Coprimary.associatedPrimes I`.  This bridges the `IsCoprimary` predicate on
subquotients and the minimal associated primes compared by the Harder–Narasimhan axioms. -/
lemma toLinearExtension_eq_min' (I : StrictIntvl (Submodule R M))
    (hu : ∃! p, p ∈ _root_.associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right))
    {p : PrimeSpectrum R}
    (hp : p.asIdeal ∈ _root_.associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)) :
    toLinearExtension p = (associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I) :=
  PrimeSpectrum.ext (hu.unique hp (min'_mem_associatedPrimes I))

/-- For the coprimary payoff function, the `max` operation is redundant: enlarging the right
endpoint only enlarges the set of associated primes, so the whole interval already realizes
the supremum. -/
lemma max_payoff : (payoff R M).max = payoff R M := by
  refine PayoffFunction.ext fun I ↦
    le_antisymm (PayoffFunction.max_le fun u hu ↦ ?_) PayoffFunction.apply_le_max
  simp only [payoff_apply]
  exact DedekindCut.principal_le_principal.mpr <| Finset.Colex.toColex_le_toColex_of_subset <|
    Set.toFinset_subset_toFinset.mpr <| associatedPrimes_mono_right hu.1 hu.2

/-- The coprimary payoff function is convex: the payoff of `(x ⊓ y, x)` is at most the
payoff of `(y, x ⊔ y)`, since the second isomorphism theorem embeds the first subquotient
into the second and subset inclusion of associated primes refines the colexicographic order.
This is Proposition 3.11 of [ChenJeannin]; the global `IsConvex` instance is derived
automatically. -/
instance [Nontrivial M] : (payoff R M).IsConvexOn ⊤ := by
  refine { le := fun x y _ _ hxy ↦ ?_ }
  simp only [payoff_apply]
  refine DedekindCut.principal_le_principal.mpr <| Finset.Colex.toColex_le_toColex_of_subset <|
    Set.toFinset_subset_toFinset.mpr ?_
  intro w hw
  rw [mem_associatedPrimes, AssociatedPrimes.mem_iff] at hw ⊢
  exact (LinearEquiv.isAssociatedPrime_iff (LinearMap.quotientInfEquivSupQuotient x y)).1 hw

/-- Lower bound property of the minimal associated prime: for an intermediate submodule
`N''` of `I`, any associated prime of `I.right ⧸ N''` is at least the minimal element of
`Coprimary.associatedPrimes I`.  Indeed, such a prime contains the annihilator of `I.right ⧸ N''`,
hence the annihilator of `I.right ⧸ I.left`; a minimal prime over that annihilator below it
is an associated prime of `I.right ⧸ I.left` (Noetherian, finite), and the chosen minimum is
below it in the linear extension. -/
private lemma min'_le_toLinearExtension (I : StrictIntvl (Submodule R M))
    (N'' : Submodule R M) (ha1 : N'' ∈ I) :
    ∀ p : PrimeSpectrum R,
      p.asIdeal ∈ _root_.associatedPrimes R (I.right ⧸ N''.submoduleOf I.right) →
      (associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I) ≤ toLinearExtension p := by
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
  refine le_trans ((associatedPrimes I).toFinset.min'_le (toLinearExtension ⟨r, hr.1.1⟩) <|
    Set.mem_toFinset.mpr <|
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hr) <|
    toLinearExtension.monotone' (hrq : (⟨r, hr.1.1⟩ : PrimeSpectrum R) ≤ p)

/-- Singleton lower bound for the first-player value: the singleton on the minimal
associated prime of `I` is below the associated primes of any right-anchored subinterval. -/
private lemma singleton_min'_le (I : StrictIntvl (Submodule R M))
    (N'' : Submodule R M) (ha1 : N'' ∈ I) (ha2 : N'' ≠ I.right) :
    toColex {(associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I)} ≤
      toColex (associatedPrimes ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset := by
  have h1 :
      toColex ({(associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I)} : Finset _) ≤
      toColex {(associatedPrimes ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'
        (associatedPrimes_nonempty _)} := by
    rw [Finset.Colex.singleton_le_singleton]
    exact min'_le_toLinearExtension I N'' ha1 _ <|
      min'_mem_associatedPrimes ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩
  exact le_trans h1 <| Finset.Colex.toColex_le_toColex_of_subset <|
    Finset.singleton_subset_iff.mpr <|
      (associatedPrimes ⟨N'', I.right, lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <|
        associatedPrimes_nonempty _

/-- The kernel of the localization map of the subquotient of `I` at (the complement of) its
minimal associated prime.  Its lift realizes the infimum defining the first-player value. -/
private noncomputable abbrev locKer (I : StrictIntvl (Submodule R M)) :
    Submodule R (↥I.right ⧸ I.left.submoduleOf I.right) :=
  LinearMap.ker (LocalizedModule.mkLinearMap
    (((associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I)).asIdeal.primeCompl)
    (↥I.right ⧸ I.left.submoduleOf I.right))

/-- The associated primes of the witness subquotient form a singleton: quotienting by the
lifted localization kernel leaves exactly the associated primes disjoint from the complement
of the minimal prime (Bourbaki), i.e. those contained in it; by minimality of the chosen
element in the linear extension, only the minimal prime remains. -/
private lemma associatedPrimes_quot_liftQuot_locKer (I : StrictIntvl (Submodule R M)) :
    _root_.associatedPrimes R
        (↥I.right ⧸ (liftQuot I.left I.right (locKer I)).submoduleOf I.right) =
      {((associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I)).asIdeal} := by
  rw [LinearEquiv.AssociatedPrimes.eq (quotLiftQuotEquiv I.left I.right (locKer I)),
    associatedPrimes_quot_ker_mkLinearMap]
  ext q
  constructor
  · rintro ⟨hq, hdisj⟩
    simp only [Set.mem_singleton_iff]
    have hle : (⟨q, hq.out.1⟩ : PrimeSpectrum R) ≤
        (associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I) :=
      Set.sdiff_eq_empty.mp hdisj
    have heq : toLinearExtension ⟨q, hq.out.1⟩ =
        (associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I) :=
      eq_of_le_of_ge (toLinearExtension.monotone' hle) <|
        (associatedPrimes I).toFinset.min'_le (toLinearExtension ⟨q, hq.out.1⟩)
          (Set.mem_toFinset.mpr hq)
    exact congrArg PrimeSpectrum.asIdeal heq
  · rintro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    refine ⟨min'_mem_associatedPrimes I, ?_⟩
    · unfold Ideal.primeCompl
      simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.inter_compl_self]

/-- The first-player value of the coprimary payoff function on any interval is the singleton
containing the *minimal* associated prime of its subquotient (in the fixed linear extension
of the prime spectrum).  The optimal first move is the lift of the localization kernel
`Coprimary.locKer`, whose subquotient has exactly the minimal prime as associated prime.
This is Proposition 3.12 of [ChenJeannin]. -/
lemma A_payoff (I : StrictIntvl (Submodule R M)) :
    (payoff R M).A I =
      .principal (toColex {(associatedPrimes I).toFinset.min' (associatedPrimes_nonempty I)}) := by
  have hmid := liftQuot_middle I.left I.right I.lt.le (locKer I)
  have hne : liftQuot I.left I.right (locKer I) ≠ I.right := fun hc ↦ by
    have : Subsingleton (↥I.right ⧸ (liftQuot I.left I.right (locKer I)).submoduleOf I.right) :=
      Submodule.Quotient.subsingleton_iff.mpr (Submodule.submoduleOf_eq_top.mpr hc.ge)
    exact Set.singleton_ne_empty _
      ((associatedPrimes_quot_liftQuot_locKer I).symm.trans
        associatedPrimes.eq_empty_of_subsingleton)
  refine le_antisymm
    (le_trans (PayoffFunction.A_le (I := I) ⟨hmid.1, lt_of_le_of_ne hmid.2 hne⟩) (le_of_eq ?_))
    (PayoffFunction.le_A fun a ha ↦ ?_)
  · rw [max_payoff, payoff_apply, DedekindCut.principal_inj, toColex_inj]
    refine (Set.toFinset_congr ?_).trans (Set.toFinset_singleton _)
    ext w
    rw [mem_associatedPrimes, associatedPrimes_quot_liftQuot_locKer I, Set.mem_singleton_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h ↦ PrimeSpectrum.ext h, fun h ↦ congrArg PrimeSpectrum.asIdeal h⟩
  · rw [max_payoff, payoff_apply]
    exact DedekindCut.principal_le_principal.mpr <| singleton_min'_le I a ⟨ha.1, ha.2.le⟩ ha.2.ne

/-- The coprimary payoff function satisfies the descending chain condition for the
first-player value: a strictly improving chain of submodules would produce infinitely many
distinct associated primes of a fixed finitely generated module, contradicting finiteness of
`associatedPrimes` over a Noetherian ring.  This is Proposition 3.13 of [ChenJeannin]. -/
instance : (payoff R M).ADCC where
  dcc := by
    intro N x hx1 hx2
    by_contra hc
    simp only [not_exists, A_payoff, DedekindCut.principal_lt_principal,
      Finset.Colex.singleton_lt_singleton, not_not] at hc
    have s1 : ∀ i, ((associatedPrimes ⟨N, x i, hx1 i⟩).toFinset.min'
          (associatedPrimes_nonempty _)).asIdeal ∈
        _root_.associatedPrimes R (↥(x i) ⧸ N.submoduleOf (x i)) :=
      fun i ↦ min'_mem_associatedPrimes ⟨N, x i, hx1 i⟩
    have s2 : ∀ i,
        _root_.associatedPrimes R (↥(x i) ⧸ N.submoduleOf (x i)) ⊆
        _root_.associatedPrimes R (↥(x 0) ⧸ N.submoduleOf (x 0)) :=
      fun i ↦ associatedPrimes_subset_of_submoduleOf_le N (x i) (x 0) (hx2.antitone i.zero_le)
    refine (_root_.associatedPrimes.finite R ((↥(x 0) ⧸ N.submoduleOf (x 0)))).not_infinite ?_
    refine Set.infinite_of_injective_forall_mem ?_ <| fun i ↦ s2 i (s1 i)
    exact fun a b hab ↦ (strictMono_nat_of_lt_succ hc).injective (PrimeSpectrum.ext hab)

/-- Semistability of the coprimary payoff function is equivalent to the first-player value
being constant on the initial segments `(⊥, N)`, equal to the singleton on the minimal
associated prime of `M`.  This is one of the equivalences of Remark 3.14 of [ChenJeannin]. -/
theorem isSemistable_iff_A_const [Nontrivial M] :
    (payoff R M).IsSemistable ↔ ∀ N : Submodule R M, (hN : ⊥ < N) →
      (payoff R M).A ⟨⊥, N, hN⟩ =
        .principal (toColex {(associatedPrimes (⊤ : StrictIntvl (Submodule R M))).toFinset.min'
          (associatedPrimes_nonempty ⊤)}) := by
  constructor
  · intro hst N hN
    have hst' : ¬ (payoff R M).A ⊤ < (payoff R M).A ⟨⊥, N, hN⟩ := hst.not_lt N hN
    rw [A_payoff ⟨⊥, N, hN⟩, A_payoff (⊤ : StrictIntvl (Submodule R M)),
      DedekindCut.principal_lt_principal, Finset.Colex.singleton_lt_singleton, not_lt] at hst'
    rw [A_payoff ⟨⊥, N, hN⟩]
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
    exact eq_of_le_of_ge hst' <| Finset.min'_subset (associatedPrimes_nonempty _) <|
      Set.toFinset_subset_toFinset.mpr <| associatedPrimes_mono_right hN le_top
  · intro h
    refine { not_lt := fun N hN ↦ ?_ }
    specialize h N hN
    rw [A_payoff ⟨⊥, N, hN⟩] at h
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj] at h
    rw [A_payoff ⟨⊥, N, hN⟩, A_payoff (⊤ : StrictIntvl (Submodule R M)),
      DedekindCut.principal_lt_principal, Finset.Colex.singleton_lt_singleton, not_lt]
    exact h.le

/-- **Semistable means coprimary**: the coprimary payoff function of `M` is semistable if
and only if `M` has exactly one associated prime.  This is the core semantic equivalence of
the chapter (Remark 3.14 of [ChenJeannin]); together with
`Coprimary.isSemistable_restrict_iff_quotient` it identifies Harder–Narasimhan filtrations
of `Coprimary.payoff R M` with coprimary filtrations of `M`. -/
theorem isSemistable_iff_existsUnique_associatedPrime [Nontrivial M] :
    (payoff R M).IsSemistable ↔ ∃! p, p ∈ _root_.associatedPrimes R M := by
  rw [isSemistable_iff_A_const]
  let p0 := (associatedPrimes (⊤ : StrictIntvl (Submodule R M))).toFinset.min'
    (associatedPrimes_nonempty ⊤)
  have hbot (N : Submodule R M) : (⊥ : Submodule R M).submoduleOf N = ⊥ :=
    Submodule.ker_subtype N
  let eTop : (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).submoduleOf ⊤) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEqBot _ (hbot ⊤)).trans Submodule.topEquiv
  have hp0 : p0.asIdeal ∈ _root_.associatedPrimes R M := by
    simpa [LinearEquiv.AssociatedPrimes.eq eTop] using
      min'_mem_associatedPrimes (⊤ : StrictIntvl (Submodule R M))
  constructor
  · refine fun hs => ⟨p0.asIdeal, hp0, fun J hJ => ?_⟩
    obtain ⟨hJp, t, ht⟩ := (isAssociatedPrime_iff (R := R) (M := M)).1 <|
      (AssociatedPrimes.mem_iff (R := R) (M := M)).1 hJ
    have htors : Ideal.torsionOf R M t = J := by
      ext a
      rw [Ideal.mem_torsionOf_iff, ht, Submodule.mem_colon_singleton, Submodule.mem_bot]
    have hN : ⊥ < (R ∙ t : Submodule R M) := by
      rw [bot_lt_iff_ne_bot, ne_eq, Submodule.span_singleton_eq_bot]
      exact fun ht0 ↦ hJp.ne_top (by rw [ht, ht0, Submodule.colon_singleton_zero])
    have hassN : _root_.associatedPrimes R ↥(R ∙ t : Submodule R M) = {J} := by
      rw [← LinearEquiv.AssociatedPrimes.eq (Ideal.quotTorsionOfEquivSpanSingleton R M t), htors,
        associatedPrimes.eq_singleton_of_isPrimary hJp.isPrimary, hJp.radical]
    have hmin : (associatedPrimes ⟨⊥, R ∙ t, hN⟩).toFinset.min'
        (associatedPrimes_nonempty _) = ⟨J, hJp⟩ := by
      have hpN : ((associatedPrimes ⟨⊥, R ∙ t, hN⟩).toFinset.min'
          (associatedPrimes_nonempty _)).asIdeal ∈
          _root_.associatedPrimes R ↥(R ∙ t : Submodule R M) := by
        simpa [LinearEquiv.AssociatedPrimes.eq
          (Submodule.quotEquivOfEqBot _ (hbot (R ∙ t)))] using
          min'_mem_associatedPrimes (⟨⊥, R ∙ t, hN⟩ : StrictIntvl (Submodule R M))
      exact PrimeSpectrum.ext (Set.mem_singleton_iff.mp (hassN ▸ hpN))
    have hs' := hs (R ∙ t) hN
    rw [A_payoff ⟨⊥, R ∙ t, hN⟩] at hs'
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj] at hs'
    exact congrArg PrimeSpectrum.asIdeal (hmin.symm.trans hs')
  · rintro ⟨p, hp, hp_unique⟩ N hN
    rw [A_payoff ⟨⊥, N, hN⟩]
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
    have hq : ((associatedPrimes ⟨⊥, N, hN⟩).toFinset.min' (associatedPrimes_nonempty _)).asIdeal ∈
        _root_.associatedPrimes R M := by
      have hI := associatedPrimes_mono_right hN le_top <|
        min'_mem_associatedPrimes (⟨⊥, N, hN⟩ : StrictIntvl (Submodule R M))
      simpa [LinearEquiv.AssociatedPrimes.eq eTop] using hI
    exact PrimeSpectrum.ext ((hp_unique _ hq).trans (hp_unique _ hp0).symm)

/-- The first-player value on an interval `(N₁, W)` inside `(N₁, N₂)` agrees with the
first-player value of the coprimary payoff function of the subquotient `N₂ ⧸ N₁` on the
image of `W`.  This is the value-level translation between the restricted game and the game
on the subquotient. -/
lemma A_restrict_eq_quotient {N₁ N₂ W : Submodule R M} (h₁ : N₁ ≤ W) (h₂ : W ≤ N₂)
    (h₃ : W ≠ N₁) :
    (payoff R M).A ⟨N₁, W, lt_of_le_of_ne h₁ (Ne.symm h₃)⟩ =
      (payoff R (↥N₂ ⧸ N₁.submoduleOf N₂)).A
        ⟨⊥, Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W),
          bot_lt_iff_ne_bot.mpr <| map_comap_ne_bot h₁ h₂ h₃⟩ := by
  rw [A_payoff, A_payoff]
  simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj]
  simp [associatedPrimes_eq_quotient h₁ h₂ h₃]

/-- Semistability of the coprimary payoff function restricted to an interval `(N₁, N₂)` of
submodules of `M` is semistability of the coprimary payoff function of the subquotient
`N₂ ⧸ N₁`.  This is the key translation step for coprimary filtrations: combined with
`Coprimary.isSemistable_iff_existsUnique_associatedPrime` it shows that the semistable
pieces of a Harder–Narasimhan filtration are exactly the coprimary subquotients. -/
lemma isSemistable_restrict_iff_quotient (N₁ N₂ : Submodule R M) (hN : N₁ < N₂) :
    ((payoff R M).restrict ⟨N₁, N₂, hN⟩).IsSemistable ↔
      letI : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
      (payoff R (↥N₂ ⧸ N₁.submoduleOf N₂)).IsSemistable := by
  refine ⟨?_, ?_⟩
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
    refine { not_lt := ?_ }
    intro X hX
    have hres := h.not_lt
      ⟨liftQuot N₁ N₂ X, liftQuot_middle N₁ N₂ (le_of_lt hN) X⟩
      (bot_lt_iff_ne_bot.2 fun hc ↦
        liftQuot_ne_left N₁ N₂ X hX.ne' (Subtype.coe_inj.mpr hc))
    have hmid := liftQuot_middle N₁ N₂ (le_of_lt hN) X
    have hneq : liftQuot N₁ N₂ X ≠ N₁ := liftQuot_ne_left N₁ N₂ X hX.ne'
    have hres' :
        ¬ (payoff R M).A ⟨N₁, N₂, hN⟩ <
          (payoff R M).A ⟨N₁, liftQuot N₁ N₂ X, lt_of_le_of_ne hmid.1 hneq.symm⟩ := by
      simp only [PayoffFunction.A_restrict_apply] at hres
      exact hres
    rw [A_restrict_eq_quotient hmid.1 hmid.2 hneq,
      A_restrict_eq_quotient (le_of_lt hN) le_rfl hN.ne.symm] at hres'
    simpa [liftQuot, Submodule.comap_map_eq, Submodule.ker_subtype,
      Submodule.map_comap_eq_self, Submodule.range_mkQ] using hres'
  · intro h
    let : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := nontrivial_quotient_of_lt hN
    refine { not_lt := ?_ }
    intro W hW
    have hW' : W.val ≠ N₁ := fun hEq ↦ hW.ne' (Subtype.ext hEq)
    have hquot := h.not_lt
      (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W.val))
      (bot_lt_iff_ne_bot.2 <| map_comap_ne_bot W.prop.1 W.prop.2 hW')
    have hquot' :
        ¬ (payoff R M).A ⟨N₁, N₂, hN⟩ <
          (payoff R M).A ⟨N₁, W.val, lt_of_le_of_ne W.prop.1 hW'.symm⟩ := by
      simpa [A_restrict_eq_quotient (N₁ := N₁) (N₂ := N₂) (W := W.val)
          W.prop.1 W.prop.2 hW',
        A_restrict_eq_quotient (N₁ := N₁) (N₂ := N₂) (W := N₂)
          (le_of_lt hN) le_rfl hN.ne.symm,
        Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ] using hquot
    simp only [PayoffFunction.A_restrict_apply]
    exact hquot'

end Payoff

end Coprimary

end HarderNarasimhan
