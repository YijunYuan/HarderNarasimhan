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

import Mathlib.Order.Completion

import HarderNarasimhan.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import Mathlib.Combinatorics.Colex

/-!
Definitions for coprimary filtrations in the Noetherian module setting.

This module specializes the general Harder–Narasimhan machinery to the following
concrete “slope” construction:

* `ℒ R M` is the lattice of submodules of a finite module `M` over a Noetherian
  commutative ring `R`.
* `S₀ R` is a finset-valued slope codomain built from linear extensions of
  `PrimeSpectrum R`, equipped with the colexicographic linear order (`Finset.Colex`).
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

We work with `Finset (LinearExtension (PrimeSpectrum R))` so that the colexicographic order
(`Finset.Colex` from mathlib) can provide a linear order compatible with subset inclusion.
-/
abbrev S₀ (R : Type*) [CommRing R]
------------
:= Finset (LinearExtension (PrimeSpectrum R))

/--
`LinearExtension` is a plain type alias, and typeclass resolution does not unfold it, so
primality of `p.asIdeal` must be restated for points of the linearly extended spectrum.
-/
instance {R : Type*} [CommRing R] (p : LinearExtension (PrimeSpectrum R)) :
    p.asIdeal.IsPrime := PrimeSpectrum.isPrime p

/--
Linear order on `S₀ R`: mathlib's colexicographic order, transported from the `Colex` type
synonym to `S₀ R` itself.

This is an intentionally “local” instance with an explicit priority, so we do not
pollute global typeclass search with a new linear order on `Finset`.
-/
noncomputable instance (priority := 114514) {R : Type*} [CommRing R] :
------------
LinearOrder (S₀ R)
------------
:= LinearOrder.lift' toColex fun _ _ h ↦ by simpa using h

/--
The induced partial order on `S₀ R`.

This is obtained by forgetting the extra structure of the linear order instance.
-/
noncomputable instance (priority := 114513) {R : Type*} [CommRing R] :
------------
PartialOrder (S₀ R)
------------
:= instLinearOrderS₀.toPartialOrder

/--
The `≤` relation on `S₀ R` exported as a standalone `LE` instance.

Some downstream definitions refer to `LE` explicitly; we expose it to avoid
unpleasant definitional equalities.
-/
noncomputable instance (priority := 114512) {R : Type*} [CommRing R] :
------------
LE (S₀ R)
------------
where
  le := instLinearOrderS₀.le

/--
Core monotonicity property of the chosen `S₀ R` order:

* subset inclusion implies `≤` on finsets, and
* for singletons, `≤` agrees with the underlying order on the linear extension.

Both are inherited from the colexicographic order. These are used throughout the coprimary
filtration construction.
-/
lemma S₀_order {R : Type*} [CommRing R] :
------------
(
  -- `⊆` on `Finset` now elaborates to `LE.le`, which the high-priority `S₀ R` order
  -- instances above would capture; the canonical subset order is pinned explicitly.
  ∀ A B : S₀ R, @LE.le (S₀ R) Finset.instPartialOrder.toLE A B → A ≤ B
) ∧
∀ a b : LinearExtension (PrimeSpectrum R), a ≤ b ↔ ({a} : (S₀ R)) ≤ ({b} : (S₀ R))
------------
:= ⟨fun _ _ h ↦ Finset.Colex.toColex_le_toColex_of_subset h,
  fun _ _ ↦ Finset.Colex.singleton_le_singleton.symm⟩

/--
Strict inequality on the linear extension matches strict inequality of singletons.

This is a convenient corollary of `S₀_order` expressed in `<` form.
-/
lemma S₀_order' {R : Type*} [CommRing R]
  {a b : LinearExtension (PrimeSpectrum R)} :
------------
a < b ↔ ({a} : (S₀ R)) < ({b} : (S₀ R))
------------
:= by
  refine le_iff_le_iff_lt_iff_lt.mp ?_
  simp only [S₀_order.2]

/--
The completed slope codomain `S R`.

We use the Dedekind–MacNeille completion (`DedekindCut` from mathlib) so that the codomain is a
complete lattice, as required by the general Harder–Narasimhan framework. The cut is taken with
respect to the colexicographic order on `S₀ R` pinned explicitly.
-/
abbrev S (R : Type*) [CommRing R]
------------
:= @DedekindCut (S₀ R) instPartialOrderS₀.toPreorder

/--
View an element of `S₀ R` as a principal cut in the completion `S R`.

This lets statements compare `μA`-values in `S R` with explicit finsets in `S₀ R`.
-/
noncomputable instance {R : Type*} [CommRing R] : Coe (S₀ R) (S R) :=
  ⟨DedekindCut.principal⟩

/--
The lattice of submodules of a finite module.

This is the base lattice `ℒ` to which we apply the general filtration theory.
-/
abbrev ℒ (R : Type*) [CommRing R]
(M : Type*) [AddCommGroup M] [Module R M]
------------
:= Submodule R M

/--
The underlying set-valued “slope”: associated primes of a quotient.

Given an interval `I : N₁ < N₂` in the submodule lattice, `_μ R M I` is the set of
linear extensions of `PrimeSpectrum R` corresponding to associated primes of the
quotient `N₂ / N₁`.

This is later turned into a finset and then coerced into the complete lattice `S R`.
-/
abbrev _μ (R : Type*) [CommRing R]
(M : Type*) [AddCommGroup M] [Module R M]
(I : StrictIntvl (ℒ R M)) :
------------
Set (LinearExtension (PrimeSpectrum R))
------------
:=
{q : LinearExtension (PrimeSpectrum R) |
  q.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)}

/--
Finiteness of `_μ R M I`.

For a Noetherian ring and a finite module, the set of associated primes of any
finitely generated module is finite; since `_μ` is its preimage under the injective map
`q ↦ q.asIdeal`, this yields a `Fintype` instance.
-/
noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : StrictIntvl (ℒ R M)} :
------------
Fintype ((_μ R M) I)
------------
:= (Set.Finite.preimage (Set.injOn_of_injective fun _ _ h ↦ PrimeSpectrum.ext h)
  (associatedPrimes.finite R (I.right ⧸ I.left.submoduleOf I.right))).fintype

/--
The slope function `μ` valued in the complete lattice `S R`.
Most downstream statements about coprimary filtrations (existence/uniqueness, convexity, etc.)
are phrased in terms of `μ R M`.

We take the finset of associated primes and coerce it into the Dedekind–MacNeille
completion.

API note: this is the primary slope map exported by the coprimary layer.
-/
noncomputable abbrev μ (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
PayoffFunction (ℒ R M) (S R)
------------
:= ⟨fun I ↦ .principal ((_μ R M) I).toFinset⟩

/--
Predicate asserting that a module is coprimary.
We define `Coprimary R M` as “the set of associated primes of `M` is a singleton”,
packaged as existence and uniqueness of such a prime.

This notion is used for the successive quotients in a coprimary filtration.

API note: this is the user-facing predicate for “coprimary successive factors”.
-/
class Coprimary (R : Type*) [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∃! p, p ∈ associatedPrimes R M

open Classical in
/--
A coprimary filtration of a finite module.
The `Nonempty`/`Unique` instances live in `HarderNarasimhan.CoprimaryFiltration.Results`.

This mirrors `HarderNarasimhanFiltration` but strengthens the “piecewise semistable”
condition to a concrete algebraic one: each successive quotient is coprimary.

Additionally, `strict_anti_associated_prime` enforces strict decrease of the associated
primes of successive factors along the filtration (in the fixed linear extension): any
associated prime of a later piece is strictly below any associated prime of an earlier piece.
Since each piece is coprimary, its set of associated primes is a singleton, so this
universally quantified form is equivalent to comparing "the" primes — but it avoids
`Exists.choose` in the statement and dependence on the proof of `piecewise_coprimary`.

API note: this is the main structure that users quantify over in the coprimary chapter.
-/
@[ext]
structure CoprimaryFiltration (R : Type*) [CommRing R] [IsNoetherianRing R]
(M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  filtration : ℕ → Submodule R M
  monotone            : Monotone filtration
  first_eq_bot        : filtration 0 = ⊥
  fin_len             : ∃ n : ℕ, filtration n = ⊤
  strict_mono         : StrictMonoOn filtration (Set.Iic (Nat.find fin_len))
  piecewise_coprimary :
    ∀ n : ℕ, n < Nat.find (fin_len) →
      Coprimary R (filtration (n+1)⧸ ((filtration n).submoduleOf (filtration (n+1))))
  strict_anti_associated_prime :
    ∀ n : ℕ, n + 1 < Nat.find (fin_len) →
      ∀ p q : PrimeSpectrum R,
        p.asIdeal ∈ associatedPrimes R
          (filtration (n+2) ⧸ (filtration (n+1)).submoduleOf (filtration (n+2))) →
        q.asIdeal ∈ associatedPrimes R
          (filtration (n+1) ⧸ (filtration n).submoduleOf (filtration (n+1))) →
        toLinearExtension p < toLinearExtension q


namespace CoprimaryFiltration

open Classical in
/--
The length of a coprimary filtration: the first index at which it reaches `⊤`.

All `Nat.find`-based bookkeeping about the chain length is encapsulated here and in the
accompanying lemmas; downstream code should use `F.length` and never touch `Nat.find` directly.
-/
noncomputable def length {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CoprimaryFiltration R M) : ℕ := Nat.find F.fin_len

open Classical in
@[simp] lemma filtration_length {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CoprimaryFiltration R M) : F.filtration F.length = ⊤ := Nat.find_spec F.fin_len

open Classical in
lemma ne_top_of_lt_length {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CoprimaryFiltration R M) {m : ℕ} (h : m < F.length) :
    F.filtration m ≠ ⊤ := Nat.find_min F.fin_len h

open Classical in
lemma length_le_of_eq_top {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CoprimaryFiltration R M) {m : ℕ} (h : F.filtration m = ⊤) :
    F.length ≤ m := Nat.find_min' F.fin_len h

end CoprimaryFiltration

end HarderNarasimhan
