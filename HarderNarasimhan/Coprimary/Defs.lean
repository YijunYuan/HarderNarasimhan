/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Defs
public import Mathlib.Combinatorics.Colex
public import Mathlib.Order.Completion
public import Mathlib.Order.Extension.Linear
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The coprimary payoff function and coprimary filtrations

For a finitely generated module `M` over a commutative Noetherian ring `R`, the coprimary
payoff function assigns to a strict inclusion `N₁ < N₂` the associated primes of
`N₂ ⧸ N₁`.

A module is *coprimary* if it has exactly one associated prime. A *coprimary filtration*
is a finite filtration with coprimary successive quotients whose associated primes strictly
decrease in a fixed linear extension of the prime spectrum. These are the Harder–Narasimhan
filtrations of the coprimary payoff function; see `HarderNarasimhan/Coprimary/Filtration.lean`.

## Main definitions

* `HarderNarasimhan.Coprimary.subquotientAssociatedPrimes`: the associated primes of a subquotient,
  viewed in the linear extension of the prime spectrum.
* `HarderNarasimhan.Coprimary.payoff`: the coprimary payoff function on the submodule lattice.
* `HarderNarasimhan.IsCoprimary`: the property of having exactly one associated prime.
* `HarderNarasimhan.CoprimaryFiltration`: a filtration with coprimary successive quotients and
  strictly decreasing associated primes.

## Implementation notes

The payoff takes values in
`DedekindCut (Colex (Finset (LinearExtension (PrimeSpectrum R))))`.
The linear extension orders the prime spectrum, and the colexicographic order on finite sets
extends inclusion and agrees with this order on singletons. The Dedekind–MacNeille completion
then gives the complete linear order required by the general theory.

A filtration is represented by a sequence indexed by `ℕ`, constant at `⊤` from its length
onwards. Its length is determined by the sequence, so
`HarderNarasimhan.CoprimaryFiltration.ext` only requires equality of the underlying sequences.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

/-- The ideal underlying a point of the linearly extended prime spectrum is prime.

This instance makes primality available without unfolding `LinearExtension`. -/
instance {R : Type*} [CommRing R] (p : LinearExtension (PrimeSpectrum R)) :
    p.asIdeal.IsPrime := PrimeSpectrum.isPrime p

namespace Coprimary

section SubquotientAssociatedPrimes

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The associated primes of `I.right ⧸ I.left`, viewed in the linearly extended prime
spectrum. -/
def subquotientAssociatedPrimes (I : StrictIntvl (Submodule R M)) :
    Set (LinearExtension (PrimeSpectrum R)) :=
  {q | q.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right)}

@[simp] lemma mem_subquotientAssociatedPrimes {I : StrictIntvl (Submodule R M)}
    {q : LinearExtension (PrimeSpectrum R)} :
    q ∈ subquotientAssociatedPrimes I ↔
      q.asIdeal ∈ associatedPrimes R (I.right ⧸ I.left.submoduleOf I.right) :=
  Iff.rfl

/-- A subquotient of a finitely generated module over a Noetherian ring has finitely many
associated primes. -/
noncomputable instance [IsNoetherianRing R] [Module.Finite R M]
    (I : StrictIntvl (Submodule R M)) : Fintype (subquotientAssociatedPrimes I) :=
  (Set.Finite.preimage (Set.injOn_of_injective fun _ _ h ↦ PrimeSpectrum.ext h)
    (associatedPrimes.finite R (I.right ⧸ I.left.submoduleOf I.right))).fintype

end SubquotientAssociatedPrimes

section Payoff

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The coprimary payoff function sends `N₁ < N₂` to the associated primes of `N₂ ⧸ N₁`,
ordered colexicographically in the linearly extended prime spectrum and embedded in the
Dedekind–MacNeille completion. -/
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

/-- A module is *coprimary* if it has exactly one associated prime. -/
class IsCoprimary : Prop where
  /-- The module has exactly one associated prime. -/
  existsUnique_associatedPrime : ∃! p, p ∈ associatedPrimes R M

end IsCoprimary

section CoprimaryFiltration

/-- A coprimary filtration is a finite chain `⊥ = F 0 < ⋯ < F F.length = ⊤` of submodules
whose successive quotients are coprimary and whose associated primes strictly decrease in
the fixed linear extension of the prime spectrum.

The chain is indexed by `ℕ` and is constant at `⊤` from `F.length` onwards. -/
structure CoprimaryFiltration (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  /-- The underlying chain; apply via the coercion, `F n`. -/
  toFun : ℕ → Submodule R M
  /-- The number of successive quotients. -/
  length : ℕ
  /-- The chain is monotone. -/
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

/-- The length is the least index at which the filtration reaches `⊤`. -/
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_top_of_lt hc h

/-- From `F.length` onwards, the chain is constantly `⊤`. -/
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ :=
  top_le_iff.1 <| F.length_eq_top ▸ F.monotone h

/-- Two coprimary filtrations with the same underlying chain are equal. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end CoprimaryFiltration

end CoprimaryFiltration

end HarderNarasimhan
