/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Order.Completion
import Mathlib.Order.Extension.Linear
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import HarderNarasimhan.PayoffFunction.Defs

/-!
# The coprimary payoff function and coprimary filtrations

This file specializes the Harder–Narasimhan game to modules: for a finite module `M` over a
Noetherian commutative ring `R`, it defines a payoff function on the lattice of submodules of
`M` whose Harder–Narasimhan filtrations are precisely the classical *coprimary filtrations*.

The payoff `Coprimary.payoff R M` of an interval `(N₁, N₂)` of submodules is the finset of
associated primes of the subquotient `N₂ ⧸ N₁`, recorded as follows:

* the primes are taken in a fixed linear extension `LinearExtension (PrimeSpectrum R)` of the
  prime spectrum, so that finsets of them can be compared;
* finsets are compared in mathlib's colexicographic order `Colex (Finset _)`, which refines
  subset inclusion and restricts to the underlying order on singletons;
* the resulting linear order is completed to the complete linear order
  `DedekindCut (Colex (Finset (LinearExtension (PrimeSpectrum R))))`, as required by the
  general theory.

The set-valued companion `Coprimary.subquotientAssociatedPrimes I` records the associated
primes of the subquotient of `I` before any bundling; it is finite (`Fintype` instance) by
Noetherianity.

A module is *coprimary* (`IsCoprimary`) when it has exactly one associated prime.  A
*coprimary filtration* (`CoprimaryFiltration`) of `M` is a finite chain
`⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤` of submodules whose successive subquotients are
coprimary with strictly decreasing associated primes.  As for
`PayoffFunction.HarderNarasimhanFiltration`, the length of the chain is stored as a `length`
field which carries no extra information: it is provably the least index at which the chain
reaches `⊤` (`CoprimaryFiltration.length_le_of_eq_top`), so extensionality
(`CoprimaryFiltration.ext`) only requires the underlying chains to agree.

## Main definitions

* `Coprimary.subquotientAssociatedPrimes` : the set of associated primes of the subquotient
  of an interval of submodules, viewed in the linear extension of the prime spectrum.
* `Coprimary.payoff` : the coprimary payoff function on the submodule lattice.
* `IsCoprimary` : the module has exactly one associated prime.
* `CoprimaryFiltration` : a filtration with coprimary subquotients and strictly decreasing
  associated primes, applied to indices via the `FunLike` coercion.

## Main results

* `CoprimaryFiltration.length_le_of_eq_top`, `ne_top_of_lt`, `eq_top_of_length_le` : the
  `length` field is the least index at which the chain reaches `⊤`.
* `CoprimaryFiltration.ext` : two coprimary filtrations with the same underlying chain are
  equal.

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

/-- `LinearExtension` is a plain type synonym, and typeclass resolution does not unfold it,
so primality of `p.asIdeal` must be restated for points of the linearly extended prime
spectrum. -/
instance {R : Type*} [CommRing R] (p : LinearExtension (PrimeSpectrum R)) :
    p.asIdeal.IsPrime := PrimeSpectrum.isPrime p

namespace Coprimary

section SubquotientAssociatedPrimes

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The set of associated primes of the subquotient of an interval: for an interval
`I : N₁ < N₂` in the submodule lattice of `M`, `subquotientAssociatedPrimes I` is the set
of points of the linearly extended prime spectrum whose ideals are associated primes of
`N₂ ⧸ N₁`.  The coprimary payoff function `Coprimary.payoff` is built from this set. -/
def subquotientAssociatedPrimes (I : StrictIntvl (Submodule R M)) :
    Set (LinearExtension (PrimeSpectrum R)) :=
  {q | q.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)}

@[simp] lemma mem_subquotientAssociatedPrimes {I : StrictIntvl (Submodule R M)}
    {q : LinearExtension (PrimeSpectrum R)} :
    q ∈ subquotientAssociatedPrimes I ↔
      q.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right) :=
  Iff.rfl

/-- Over a Noetherian ring, a finite module has finitely many associated primes, and
`subquotientAssociatedPrimes I` is the preimage of the associated primes of the subquotient
of `I` under the injection `q ↦ q.asIdeal`; hence it is a `Fintype`. -/
noncomputable instance [IsNoetherianRing R] [Module.Finite R M]
    (I : StrictIntvl (Submodule R M)) : Fintype (subquotientAssociatedPrimes I) :=
  (Set.Finite.preimage (Set.injOn_of_injective fun _ _ h ↦ PrimeSpectrum.ext h)
    (associatedPrimes.finite R (I.right ⧸ I.left.submoduleOf I.right))).fintype

end SubquotientAssociatedPrimes

section Payoff

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The **coprimary payoff function** on the lattice of submodules of a finite module `M`
over a Noetherian commutative ring `R`: an interval `(N₁, N₂)` is sent to the finset of
associated primes of `N₂ ⧸ N₁`, compared in the colexicographic order on finsets of the
linearly extended prime spectrum and viewed in its Dedekind–MacNeille completion.

The Harder–Narasimhan filtration of this payoff function is the coprimary filtration of `M`;
see `HarderNarasimhan.Coprimary.Filtration`. -/
noncomputable def payoff :
    PayoffFunction (Submodule R M)
      (DedekindCut (Colex (Finset (LinearExtension (PrimeSpectrum R))))) :=
  ⟨fun I ↦ .principal (toColex (subquotientAssociatedPrimes I).toFinset)⟩

@[simp] lemma payoff_apply (I : StrictIntvl (Submodule R M)) :
    payoff R M I = .principal (toColex (subquotientAssociatedPrimes I).toFinset) :=
  rfl

end Payoff

end Coprimary

section IsCoprimary

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- A module is *coprimary* if it has exactly one associated prime.  This is the classical
condition on the successive subquotients of a coprimary filtration; it is equivalent to
semistability of the coprimary payoff function
(`Coprimary.isSemistable_iff_existsUnique_associatedPrime`). -/
class IsCoprimary : Prop where
  /-- The module has exactly one associated prime. -/
  existsUnique_associatedPrime : ∃! p, p ∈ associatedPrimes R M

end IsCoprimary

section CoprimaryFiltration

/-- A **coprimary filtration** of a finite module `M` over a Noetherian commutative ring
`R`: a finite chain `⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤` of submodules, extended constantly
by `⊤` above `length`, whose successive subquotients are coprimary and whose associated
primes strictly decrease along the chain (in the fixed linear extension of the prime
spectrum).  Since each subquotient is coprimary, its set of associated primes is a
singleton, so the universally quantified field `associatedPrime_succ_lt` is equivalent to
comparing "the" primes — but it avoids `Exists.choose` in the statement.

`length` is stored as data but carries no extra information: it is provably the *least*
index at which the chain reaches `⊤` (`length_le_of_eq_top`), hence determined by `toFun`;
accordingly `ext` only asks for `toFun` to agree. -/
structure CoprimaryFiltration (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  /-- The underlying chain; apply via the coercion, `F n`. -/
  toFun : ℕ → Submodule R M
  /-- The index at which the chain reaches `⊤`. -/
  length : ℕ
  /-- The chain is monotone (constantly `⊤` above `length`). -/
  monotone : Monotone toFun
  /-- The chain starts at `⊥`. -/
  head_eq_bot : toFun 0 = ⊥
  /-- The chain reaches `⊤` at index `length`. -/
  length_eq_top : toFun length = ⊤
  /-- The chain is strictly increasing up to `length`. -/
  strictMonoOn : StrictMonoOn toFun (Set.Iic length)
  /-- Each successive subquotient `F (i + 1) ⧸ F i` is coprimary. -/
  piecewise_isCoprimary : ∀ i < length,
    IsCoprimary R (toFun (i + 1) ⧸ (toFun i).submoduleOf (toFun (i + 1)))
  /-- The associated primes of the successive subquotients strictly decrease along the
  chain, in the fixed linear extension of the prime spectrum. -/
  associatedPrime_succ_lt : ∀ i, i + 1 < length → ∀ p q : PrimeSpectrum R,
    p.asIdeal ∈ associatedPrimes R
      (toFun (i + 2) ⧸ (toFun (i + 1)).submoduleOf (toFun (i + 2))) →
    q.asIdeal ∈ associatedPrimes R
      (toFun (i + 1) ⧸ (toFun i).submoduleOf (toFun (i + 1))) →
    toLinearExtension p < toLinearExtension q

namespace CoprimaryFiltration

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

instance : FunLike (CoprimaryFiltration R M) ℕ (Submodule R M) where
  coe := toFun
  coe_injective := by
    have key : ∀ F G : CoprimaryFiltration R M, F.toFun = G.toFun → F.length ≤ G.length := by
      intro F G h
      by_contra hc
      rw [not_le] at hc
      have h1 := F.strictMonoOn hc.le (Set.mem_Iic.2 le_rfl) hc
      rw [F.length_eq_top, h, G.length_eq_top] at h1
      exact lt_irrefl ⊤ h1
    intro F G h
    have hlen : F.length = G.length := le_antisymm (key F G h) (key G F h.symm)
    cases F
    cases G
    dsimp only at h hlen
    subst h
    subst hlen
    rfl

@[simp] lemma toFun_eq_coe (F : CoprimaryFiltration R M) : F.toFun = ⇑F := rfl

variable {F G : CoprimaryFiltration R M} {m : ℕ}

/-- Below `F.length` the chain has not yet reached `⊤`. -/
lemma ne_top_of_lt (h : m < F.length) : F m ≠ ⊤ := fun hc ↦
  (F.strictMonoOn h.le (Set.mem_Iic.2 le_rfl) h).ne (hc.trans F.length_eq_top.symm)

/-- Minimality of the `length` field: it is the least index at which the chain reaches
`⊤`.  In particular `length` is determined by the underlying chain. -/
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_top_of_lt hc h

/-- Above `F.length` the chain is constantly `⊤`. -/
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ :=
  top_le_iff.1 <| F.length_eq_top ▸ F.monotone h

/-- Two coprimary filtrations with the same underlying chain are equal: the `length` field
is determined by the chain (`length_le_of_eq_top`) and the remaining fields are proofs. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end CoprimaryFiltration

end CoprimaryFiltration

end HarderNarasimhan
