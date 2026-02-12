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
import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.OrderTheory.Lex'Order

namespace HarderNarasimhan

abbrev S₀ (R : Type*) [CommRing R] [IsNoetherianRing R]
------------
:= Finset (LinearExtension (PrimeSpectrum R))

noncomputable instance (priority := 114514) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
LinearOrder (S₀ R)
------------
:= (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose

noncomputable instance (priority := 114513) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
PartialOrder (S₀ R)
------------
:= instLinearOrderS₀.toPartialOrder

noncomputable instance (priority := 114512) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
LE (S₀ R)
------------
where
  le := instLinearOrderS₀.le

lemma S₀_order {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
(
  ∀ A B : S₀ R, A ⊆ B → A ≤ B
) ∧
∀ a b : LinearExtension (PrimeSpectrum R), a ≤ b ↔ ({a} : (S₀ R)) ≤ ({b} : (S₀ R))
------------
:= (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose_spec

lemma S₀_order' {R : Type*} [CommRing R] [IsNoetherianRing R]
  {a b : LinearExtension (PrimeSpectrum R)} :
------------
a < b ↔ ({a} : (S₀ R)) < ({b} : (S₀ R))
------------
:= by
  refine le_iff_le_iff_lt_iff_lt.mp ?_
  simp only [S₀_order.2]

abbrev S (R : Type*) [CommRing R] [IsNoetherianRing R]
------------
:= @OrderTheory.DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

abbrev ℒ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
------------
:= Submodule R M

abbrev _μ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
------------
Set (LinearExtension (PrimeSpectrum R))
------------
:=
{ {asIdeal := p, isPrime := h.out.1} |
  (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(I.val.1.submoduleOf I.val.2))) }

noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}} :
------------
Fintype ((_μ R M) I)
------------
:= (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(I.val.1.submoduleOf I.val.2)))
  (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

noncomputable abbrev μ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R)
------------
:= fun I ↦ ↑((_μ R M) I).toFinset

class Coprimary (R : Type*) [CommRing R] [IsNoetherianRing R]
  (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∃! p, p ∈ associatedPrimes R M

open Classical in
@[ext]
structure CoprimaryFiltration (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  filtration : ℕ → Submodule R M
  monotone            : Monotone filtration
  first_eq_bot        : filtration 0 = ⊥
  fin_len             : ∃ n : ℕ, filtration n = ⊤
  strict_mono         :
    ∀ i j : ℕ,
      i < j → j ≤ Nat.find (fin_len) →
        filtration i < filtration j
  piecewise_coprimary :
    ∀ n : ℕ, n < Nat.find (fin_len) →
      Coprimary R (filtration (n+1)⧸ ((filtration n).submoduleOf (filtration (n+1))))
  strict_mono_associated_prime :
    ∀ n : ℕ, (hn : n + 1 < Nat.find (fin_len)) →
        @LT.lt (LinearExtension (PrimeSpectrum R)) Preorder.toLT
        ({
          asIdeal := (piecewise_coprimary (n+1) hn).coprimary.exists.choose,
          isPrime := (piecewise_coprimary (n+1) hn).coprimary.exists.choose_spec.out.1
          })
        ({
          asIdeal := (piecewise_coprimary n (Nat.lt_of_succ_lt hn)).coprimary.exists.choose,
          isPrime := (piecewise_coprimary n (Nat.lt_of_succ_lt hn)
            ).coprimary.exists.choose_spec.out.1
          })


end HarderNarasimhan
