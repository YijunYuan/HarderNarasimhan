import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs

namespace HardarNarasimhan

abbrev S₀ (R : Type) [CommRing R] [IsNoetherianRing R] := Finset (LinearExtension (PrimeSpectrum R))

lemma po (R : Type) [CommRing R] [IsNoetherianRing R] : ∃ lo: LinearOrder (S₀ R),  (∀ x y : (S₀ R), x ≤ y → lo.le x y) ∧ ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ lo.le ({p} : (S₀ R)) {q} := by
  sorry

noncomputable instance (priority:=114514) {R : Type} [CommRing R] [IsNoetherianRing R]: LinearOrder (S₀ R) := (po R).choose
noncomputable instance (priority:=114513) {R : Type} [CommRing R] [IsNoetherianRing R]: PartialOrder (S₀ R) := instLinearOrderS₀.toPartialOrder
noncomputable instance (priority:=114512) {R : Type} [CommRing R] [IsNoetherianRing R]: LE (S₀ R) where
  le := instLinearOrderS₀.le

lemma S₀_order {R : Type} [CommRing R] [IsNoetherianRing R]: ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ ({p} : (S₀ R)) ≤ ({q} : (S₀ R)) := (po R).choose_spec.2

abbrev S (R : Type) [CommRing R] [IsNoetherianRing R] := @DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

abbrev ℒ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:= Submodule R M

noncomputable abbrev μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R) := fun I ↦ coe'.toFun <| @Set.toFinset (LinearExtension (PrimeSpectrum R)) ({ {asIdeal := p, isPrime := h.out.1} | (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(I.val.1.comap I.val.2.subtype))) }) <| (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(I.val.1.comap I.val.2.subtype))) (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

lemma strip_μ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, ∃ J : (S₀ R), ↑J = (μ R M) I := by
  intro _
  apply exists_apply_eq_apply

lemma μ_nonempty {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]  [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (strip_μ I).choose.Nonempty := by
  intro I
  rw [coe'.inj.1 (strip_μ I).choose_spec]
  simp only [Set.toFinset_nonempty]
  have := Submodule.Quotient.nontrivial_of_lt_top (I.val.1.comap I.val.2.subtype) <| Classical.byContradiction fun this ↦ (ne_of_lt <| lt_of_lt_of_le I.prop <| Submodule.comap_subtype_eq_top.mp <| not_lt_top_iff.1 this) rfl
  rcases associatedPrimes.nonempty R (I.val.2⧸(I.val.1.comap I.val.2.subtype)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_setOf.mpr ?_⟩
  use q, hq

lemma noname {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := sorry

lemma prop_3_11 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := sorry

lemma prop_3_12 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I = ({((strip_μ I).choose.min' <| μ_nonempty I)} : S₀ R) := by
  intro I

  sorry

instance prop_3_13 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μA_DescendingChainCondition (μ R M) where
  μ_dcc := by
    sorry

lemma rmk4d14₁ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨(⊥,N),hN⟩ = ({((strip_μ ⟨(⊥,N),hN⟩).choose.min' <| μ_nonempty ⟨(⊥,N),hN⟩)} : S₀ R) := sorry

class Coprimary (R : Type) [CommRing R] [IsNoetherianRing R](M : Type) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∀ x : R, (∃ m : M, m ≠ 0 ∧ x • m = 0) → ∃ n : Nat, n > 0 ∧ x^n ∈ Module.annihilator R M

theorem Coprimary_iff  {R : Type} [CommRing R] [IsNoetherianRing R] {M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Coprimary R M ↔ ∃! p, p ∈ associatedPrimes R M := sorry

lemma rmk4d14₂ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := sorry

open Classical

structure CoprimaryFiltration (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  filtration : ℕ → (ℒ R M)
  monotone : Monotone filtration
  first_eq_bot : filtration 0 = ⊥
  fin_len : ∃ n : ℕ, filtration n = ⊤
  strict_mono : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration i < filtration j
  coprimary : ∀ n : ℕ, n < Nat.find (fin_len) → Coprimary R (filtration (n+1)⧸ ((filtration n).comap (filtration (n+1)).subtype))

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Inhabited (CoprimaryFiltration R M) := sorry

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Nonempty (CoprimaryFiltration R M) := inferInstance

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Unique (CoprimaryFiltration R M) := sorry


end HardarNarasimhan
