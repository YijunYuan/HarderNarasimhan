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

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.OrderTheory.Lex'Order

/-!
Definitions for coprimary filtrations in the Noetherian module setting.

This module specializes the general Harder–Narasimhan machinery to the following
concrete “slope” construction:

* `ℒ R M` is the lattice of submodules of a finite module `M` over a Noetherian
  commutative ring `R`.
* `S₀ R` is a finset-valued slope codomain built from linear extensions of
  `PrimeSpectrum R`, equipped with a custom linear order (`Lex'Order`).
* `S R` is the Dedekind–MacNeille completion of `S₀ R`, making it a complete lattice.
* `μ R M` assigns to each strict inclusion of submodules the finset of associated
  primes of the corresponding quotient, coerced into `S R`.

Using this slope, a Harder–Narasimhan filtration becomes a filtration of submodules
whose successive quotients are semistable. In this file we additionally introduce
`Coprimary` and `CoprimaryFiltration`, which capture the classical notion of a
filtration with coprimary successive factors and strictly increasing associated
primes.

API overview:

* Import this file to work with the coprimary-specialised slope construction (`S₀`, `S`, `μ`) and
  the associated structures/predicates (`Coprimary`, `CoprimaryFiltration`).
* For theorems and instances that connect this slope to the general HN filtration framework,
  import `HarderNarasimhan.CoprimaryFiltration.Results`.
-/

namespace HarderNarasimhan

/--
The “discrete” slope codomain: finsets of a linearly extended prime spectrum.

We work with `Finset (LinearExtension (PrimeSpectrum R))` so that `Lex'Order` can
provide a linear order compatible with subset inclusion.
-/
abbrev S₀ (R : Type*) [CommRing R] [IsNoetherianRing R]
------------
:= Finset (LinearExtension (PrimeSpectrum R))

/--
Linear order on `S₀ R` induced by `Lex'Order`.

This is an intentionally “local” instance with an explicit priority, so we do not
pollute global typeclass search with a new linear order on `Finset`.
-/
noncomputable instance (priority := 114514) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
LinearOrder (S₀ R)
------------
:= (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose

/--
The induced partial order on `S₀ R`.

This is obtained by forgetting the extra structure of the linear order instance.
-/
noncomputable instance (priority := 114513) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
PartialOrder (S₀ R)
------------
:= instLinearOrderS₀.toPartialOrder

/--
The `≤` relation on `S₀ R` exported as a standalone `LE` instance.

Some downstream definitions refer to `LE` explicitly; we expose it to avoid
unpleasant definitional equalities.
-/
noncomputable instance (priority := 114512) {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
LE (S₀ R)
------------
where
  le := instLinearOrderS₀.le

/--
Core monotonicity property of the chosen `S₀ R` order.

This packages two facts provided by `Lex'Order_prop`:

* subset inclusion implies `≤` on finsets, and
* for singletons, `≤` agrees with the underlying order on the linear extension.

These are used throughout the coprimary filtration construction.
-/
lemma S₀_order {R : Type*} [CommRing R] [IsNoetherianRing R] :
------------
(
  ∀ A B : S₀ R, A ⊆ B → A ≤ B
) ∧
∀ a b : LinearExtension (PrimeSpectrum R), a ≤ b ↔ ({a} : (S₀ R)) ≤ ({b} : (S₀ R))
------------
:= (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose_spec

/--
Strict inequality on the linear extension matches strict inequality of singletons.

This is a convenient corollary of `S₀_order` expressed in `<` form.
-/
lemma S₀_order' {R : Type*} [CommRing R] [IsNoetherianRing R]
  {a b : LinearExtension (PrimeSpectrum R)} :
------------
a < b ↔ ({a} : (S₀ R)) < ({b} : (S₀ R))
------------
:= by
  refine le_iff_le_iff_lt_iff_lt.mp ?_
  simp only [S₀_order.2]

/--
The completed slope codomain `S R`.

We use the Dedekind–MacNeille completion so that the codomain is a complete lattice,
as required by the general Harder–Narasimhan framework.
-/
abbrev S (R : Type*) [CommRing R] [IsNoetherianRing R]
------------
:= @OrderTheory.DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

/--
The lattice of submodules of a finite module.

This is the base lattice `ℒ` to which we apply the general filtration theory.
-/
abbrev ℒ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
------------
:= Submodule R M

/--
The underlying set-valued “slope”: associated primes of a quotient.

Given an interval `I : N₁ < N₂` in the submodule lattice, `_μ R M I` is the set of
linear extensions of `PrimeSpectrum R` corresponding to associated primes of the
quotient `N₂ / N₁`.

This is later turned into a finset and then coerced into the complete lattice `S R`.
-/
abbrev _μ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
------------
Set (LinearExtension (PrimeSpectrum R))
------------
:=
{ {asIdeal := p, isPrime := h.out.1} |
  (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(I.val.1.submoduleOf I.val.2))) }

/--
Finiteness of `_μ R M I`.

For a Noetherian ring and a finite module, the set of associated primes of any
finitely generated module is finite; this yields a `Fintype` instance.
-/
noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}} :
------------
Fintype ((_μ R M) I)
------------
:= (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(I.val.1.submoduleOf I.val.2)))
  (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

/--
The slope function `μ` valued in the complete lattice `S R`.
Most downstream statements about coprimary filtrations (existence/uniqueness, convexity, etc.)
are phrased in terms of `μ R M`.

We take the finset of associated primes and coerce it into the Dedekind–MacNeille
completion.

API note: this is the primary slope map exported by the coprimary layer.
-/
noncomputable abbrev μ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R)
------------
:= fun I ↦ ↑((_μ R M) I).toFinset

/--
Predicate asserting that a module is coprimary.
We define `Coprimary R M` as “the set of associated primes of `M` is a singleton”,
packaged as existence and uniqueness of such a prime.

This notion is used for the successive quotients in a coprimary filtration.

API note: this is the user-facing predicate for “coprimary successive factors”.
-/
class Coprimary (R : Type*) [CommRing R] [IsNoetherianRing R]
  (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∃! p, p ∈ associatedPrimes R M

open Classical in
/--
A coprimary filtration of a finite module.
The `Nonempty`/`Unique` instances live in `HarderNarasimhan.CoprimaryFiltration.Results`.

This mirrors `HarderNarasimhanFiltration` but strengthens the “piecewise semistable”
condition to a concrete algebraic one: each successive quotient is coprimary.

Additionally, `strict_mono_associated_prime` enforces a strict monotonicity condition
on the associated primes of successive factors (using the fixed linear extension).

API note: this is the main structure that users quantify over in the coprimary chapter.
-/
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
