import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.Extension.Linear
import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.DedekindMacNeilleCompletion
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
namespace HardarNarasimhan

section

variable (R : Type) [CommRing R] [IsNoetherianRing R]
variable (M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

--abbrev ℒ : Type := Submodule R M
--notation ℒ := Submodule R M

variable (p : Submodule R M) (q : Submodule R M)
#check p ≤ q

abbrev S₀ (R : Type) [CommRing R] [IsNoetherianRing R] := Finset (LinearExtension (PrimeSpectrum R))

instance {R : Type} [CommRing R] [IsNoetherianRing R] : HasSubset (S₀ R)
:= inferInstance

instance {R : Type} [CommRing R] [IsNoetherianRing R] : LE (S₀ R) := inferInstance

instance {R : Type} [CommRing R] [IsNoetherianRing R] : Singleton (LinearExtension (PrimeSpectrum R)) (S₀ R) := inferInstance

lemma po (R : Type) [CommRing R] [IsNoetherianRing R] : ∃ lo: LinearOrder (S₀ R),  (∀ x y : (S₀ R), x ≤ y → lo.le x y) ∧ ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ lo.le ({p} : (S₀ R)) {q} := by
  sorry

noncomputable instance (priority:=114514) {R : Type} [CommRing R] [IsNoetherianRing R]: LinearOrder (S₀ R) := (po R).choose
noncomputable instance (priority:=114513) {R : Type} [CommRing R] [IsNoetherianRing R]: PartialOrder (S₀ R) := instLinearOrderS₀.toPartialOrder
noncomputable instance (priority:=114512) {R : Type} [CommRing R] [IsNoetherianRing R]: LE (S₀ R) where
  le := instLinearOrderS₀.le

lemma S₀_order {R : Type} [CommRing R] [IsNoetherianRing R]: ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ ({p} : (S₀ R)) ≤ ({q} : (S₀ R)) := (po R).choose_spec.2

abbrev S (R : Type) [CommRing R] [IsNoetherianRing R] := @DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

def sb (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M]
{I₁ I₂ : Submodule R M} (h : I₁ ≤ I₂) : Submodule R I₂ where
  carrier := {x | x.val ∈ I₁}
  add_mem' := by
    refine fun {a b} a_1 a_2 ↦ ?_
    simp at *
    exact (Submodule.add_mem_iff_right I₁ a_1).mpr a_2
  smul_mem' := by
    intro c x hx
    simp at *
    exact Submodule.smul_mem I₁ c hx
  zero_mem' := by
    simp

abbrev ℒ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:= Submodule R M

--instance {R : Type} [CommRing R] [IsNoetherianRing R]
--{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]: LT (ℒ R M) where
--  lt := fun p q => p < q

noncomputable abbrev μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R) := by
  intro I
  let W : Set (LinearExtension (PrimeSpectrum R)) :={ {asIdeal := p, isPrime := h.out.1} | (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(sb R M (le_of_lt I.prop)))) }
  have : W.Finite := by
    exact Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(sb R M (le_of_lt I.prop)))) (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))
  have : Fintype W := this.fintype
  exact ↑W.toFinset

lemma noname {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := sorry

lemma prop_3_11 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := sorry

lemma prop_3_12 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : True := sorry

end

end HardarNarasimhan
