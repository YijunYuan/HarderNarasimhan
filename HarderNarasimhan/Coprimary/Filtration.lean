/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Coprimary.Semistability
import HarderNarasimhan.Filtration.Unique

/-!
# Existence and uniqueness of coprimary filtrations

This file identifies the coprimary filtrations of a finite module `M` over a Noetherian
commutative ring `R` with the Harder–Narasimhan filtrations of the coprimary payoff function
`Coprimary.payoff R M`, and derives existence and uniqueness.

In one direction, the subquotients of any Harder–Narasimhan filtration of
`Coprimary.payoff R M` are coprimary
(`PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary`), so the canonical
filtration `(Coprimary.payoff R M).hnFiltration` yields the canonical coprimary filtration
`Coprimary.coprimaryFiltration R M`.  In the other direction, every coprimary filtration
underlies a Harder–Narasimhan filtration (`CoprimaryFiltration.exists_hnFiltration`);
since the payoff codomain is a complete linear order, the Harder–Narasimhan filtration is
unique, and therefore so is the coprimary filtration.

## Main definitions

* `Coprimary.coprimaryFiltration` : the canonical coprimary filtration of `M`, also
  available as `default` via the `Inhabited` instance.

## Main results

* `PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary` : the subquotients of a
  Harder–Narasimhan filtration of the coprimary payoff function are coprimary.
* `CoprimaryFiltration.exists_hnFiltration` : every coprimary filtration underlies a
  Harder–Narasimhan filtration of the coprimary payoff function.
* `Unique (CoprimaryFiltration R M)` : existence and uniqueness of the coprimary
  filtration.  This is Theorem 3.15 of [ChenJeannin].

## References

* [Chen–Jeannin, *Harder–Narasimhan game*][ChenJeannin]
-/

namespace HarderNarasimhan

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- The subquotients of a Harder–Narasimhan filtration of the coprimary payoff function are
coprimary: each step is semistable, semistability of the restriction translates to
semistability on the subquotient (`Coprimary.isSemistable_restrict_iff_quotient`), and the
latter is coprimarity (`Coprimary.isSemistable_iff_existsUnique_associatedPrime`). -/
lemma PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : (Coprimary.payoff R M).HarderNarasimhanFiltration) :
    ∀ i < F.length, IsCoprimary R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
  intro i hi
  have hstep := F.strictMonoOn hi.le hi (lt_add_one i)
  have := Coprimary.nontrivial_quotient_of_lt hstep
  exact ⟨Coprimary.isSemistable_iff_existsUnique_associatedPrime.mp <|
    (Coprimary.isSemistable_restrict_iff_quotient _ _ hstep).mp
      (F.piecewise_isSemistable i hi)⟩

namespace Coprimary

variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

variable (R M) in
/-- The **canonical coprimary filtration** of a finite module `M` over a Noetherian
commutative ring `R`: the canonical Harder–Narasimhan filtration of the coprimary payoff
function `Coprimary.payoff R M`, with the coprimarity of its subquotients supplied by
`PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary` and the strict decrease of
their associated primes extracted from the strict decrease of the first-player values via
`Coprimary.A_payoff`.  This is the existence half of Theorem 3.15 of [ChenJeannin]; by the
`Unique` instance below it is the *only* coprimary filtration of `M`. -/
noncomputable def coprimaryFiltration : CoprimaryFiltration R M :=
  let F := (payoff R M).hnFiltration
  { toFun := ⇑F
    length := F.length
    monotone := F.monotone
    head_eq_bot := F.head_eq_bot
    length_eq_top := F.length_eq_top
    strictMonoOn := F.strictMonoOn
    piecewise_isCoprimary := F.piecewise_isCoprimary
    associatedPrime_succ_lt := by
      intro n hn p q hp hq
      have h1 : (payoff R M).A ⟨F (n + 1), F (n + 2),
          F.strictMonoOn hn.le hn (lt_add_one (n + 1))⟩ <
        (payoff R M).A ⟨F n, F (n + 1),
          F.strictMonoOn (Nat.le_of_succ_le hn.le) (Nat.le_of_succ_le hn) (lt_add_one n)⟩ :=
        lt_of_not_ge (F.not_A_le_succ n hn)
      rw [A_payoff, A_payoff, DedekindCut.principal_lt_principal,
        Finset.Colex.singleton_lt_singleton] at h1
      rw [toLinearExtension_eq_min' ⟨F (n + 1), F (n + 2),
          F.strictMonoOn hn.le hn (lt_add_one (n + 1))⟩
          (F.piecewise_isCoprimary (n + 1) hn).existsUnique_associatedPrime hp,
        toLinearExtension_eq_min' ⟨F n, F (n + 1),
          F.strictMonoOn (Nat.le_of_succ_le hn.le) (Nat.le_of_succ_le hn) (lt_add_one n)⟩
          (F.piecewise_isCoprimary n (Nat.lt_of_succ_lt hn)).existsUnique_associatedPrime hq]
      exact h1 }

/-- Coprimary filtrations exist; the default is the canonical one. -/
noncomputable instance : Inhabited (CoprimaryFiltration R M) := ⟨coprimaryFiltration R M⟩

instance : Nonempty (CoprimaryFiltration R M) := inferInstance

end Coprimary

namespace CoprimaryFiltration

variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Every coprimary filtration underlies a Harder–Narasimhan filtration of the coprimary
payoff function: the chain is reused as is, piecewise semistability is coprimarity of the
subquotients read through `Coprimary.isSemistable_restrict_iff_quotient`, and the strict
decrease of the first-player values is the strict decrease of the minimal associated primes
via `Coprimary.A_payoff`. -/
lemma exists_hnFiltration (a : CoprimaryFiltration R M) :
    ∃ F : (Coprimary.payoff R M).HarderNarasimhanFiltration, ⇑a = ⇑F :=
  ⟨{ toFun := ⇑a
     length := a.length
     monotone := a.monotone
     head_eq_bot := a.head_eq_bot
     length_eq_top := a.length_eq_top
     strictMonoOn := a.strictMonoOn
     piecewise_isSemistable := fun i hi ↦ by
       have hstep := a.strictMonoOn hi.le hi (lt_add_one i)
       have := Coprimary.nontrivial_quotient_of_lt hstep
       exact (Coprimary.isSemistable_restrict_iff_quotient _ _ hstep).mpr <|
         Coprimary.isSemistable_iff_existsUnique_associatedPrime.mpr
           (a.piecewise_isCoprimary i hi).existsUnique_associatedPrime
     not_A_le_succ := fun i hi ↦ by
       rw [Coprimary.A_payoff, Coprimary.A_payoff, not_le,
         DedekindCut.principal_lt_principal, Finset.Colex.singleton_lt_singleton]
       exact a.associatedPrime_succ_lt i hi _ _
         (Coprimary.min'_mem_assPrimes ⟨a (i + 1), a (i + 2),
           a.strictMonoOn hi.le hi (lt_add_one (i + 1))⟩)
         (Coprimary.min'_mem_assPrimes ⟨a i, a (i + 1),
           a.strictMonoOn (Nat.le_of_succ_le hi.le) (Nat.le_of_succ_le hi)
             (lt_add_one i)⟩) }, rfl⟩

/-- The chain underlying any coprimary filtration is the canonical Harder–Narasimhan
filtration, by uniqueness of the latter over the complete linear payoff codomain. -/
private lemma coe_eq_hnFiltration (a : CoprimaryFiltration R M) :
    ⇑a = ⇑((Coprimary.payoff R M).hnFiltration) := by
  obtain ⟨F, hF⟩ := exists_hnFiltration a
  rw [hF, Subsingleton.elim F ((Coprimary.payoff R M).hnFiltration)]

/-- Uniqueness of the coprimary filtration: any two coprimary filtrations of `M` share the
underlying chain of the canonical Harder–Narasimhan filtration, hence are equal.  Together
with the `Inhabited` instance this is Theorem 3.15 of [ChenJeannin]. -/
noncomputable instance : Unique (CoprimaryFiltration R M) where
  uniq a := by
    ext n
    rw [coe_eq_hnFiltration a, coe_eq_hnFiltration default]

end CoprimaryFiltration

end HarderNarasimhan
