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
  filtration.
* `CoprimaryFiltration.associatedPrimes_eq_iUnion` : the associated primes of `M` are
  exactly the associated primes of the subquotients of the coprimary filtration.

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
`Coprimary.A_payoff`.  By the `Unique` instance below it is the *only* coprimary filtration
of `M`. -/
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
         (Coprimary.min'_mem_associatedPrimes ⟨a (i + 1), a (i + 2),
           a.strictMonoOn hi.le hi (lt_add_one (i + 1))⟩)
         (Coprimary.min'_mem_associatedPrimes ⟨a i, a (i + 1),
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
with the `Inhabited` instance this shows every finite module over a Noetherian commutative
ring admits exactly one coprimary filtration. -/
noncomputable instance : Unique (CoprimaryFiltration R M) where
  uniq a := by
    ext n
    rw [coe_eq_hnFiltration a, coe_eq_hnFiltration default]

/-- The associated primes of `M` are exactly the associated primes of the subquotients of
its coprimary filtration.  As each subquotient is coprimary, the right-hand side is the set
of "the" associated primes of the subquotients, which are pairwise distinct by the strict
decrease along the filtration; the coprimary filtration therefore computes
`associatedPrimes R M`.

The inclusion `⊆` is the classical dévissage of associated primes along a filtration
(`associatedPrimes.subset_union_of_exact`), valid for any filtration.  The reverse inclusion
identifies the filtration with the canonical Harder–Narasimhan filtration of the coprimary
payoff function: the first-player values of the intervals `(⊥, F (i + 1))` and
`(F i, F (i + 1))` agree (`PayoffFunction.hnFiltration_A_bot_eq_A`), and both compute
minimal associated primes (`Coprimary.A_payoff`), which places the associated prime of each
subquotient inside `associatedPrimes R M`. -/
theorem associatedPrimes_eq_iUnion (F : CoprimaryFiltration R M) :
    associatedPrimes R M =
      ⋃ i < F.length, associatedPrimes R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
  apply subset_antisymm
  · have key : ∀ k, k ≤ F.length →
        associatedPrimes R ↥(F k) ⊆
          ⋃ i < F.length, associatedPrimes R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
      intro k
      induction k with
      | zero =>
        intro _
        have h0 : F 0 = (⊥ : Submodule R M) := F.head_eq_bot
        have hsub : Subsingleton ↥(F 0) := by rw [h0]; infer_instance
        rw [associatedPrimes.eq_empty_of_subsingleton]
        exact Set.empty_subset _
      | succ k ih =>
        intro hk
        have hk' : k ≤ F.length := (Nat.le_succ k).trans hk
        have hsub := associatedPrimes.subset_union_of_exact
          (Submodule.injective_subtype ((F k).submoduleOf (F (k + 1))))
          (LinearMap.exact_subtype_mkQ ((F k).submoduleOf (F (k + 1))))
        have hle : F k ≤ F (k + 1) := F.monotone (Nat.le_succ k)
        have hAss : associatedPrimes R ↥((F k).submoduleOf (F (k + 1))) =
            associatedPrimes R ↥(F k) :=
          LinearEquiv.AssociatedPrimes.eq (Submodule.comapSubtypeEquivOfLe hle)
        intro q hq
        rcases hsub hq with h | h
        · exact ih hk' (hAss ▸ h)
        · exact Set.mem_iUnion₂.mpr ⟨k, Nat.lt_of_succ_le hk, h⟩
    intro q hq
    have hq' : q ∈ associatedPrimes R ↥(F F.length) := by
      have hEq : F F.length = (⊤ : Submodule R M) := F.length_eq_top
      rw [hEq, LinearEquiv.AssociatedPrimes.eq (Submodule.topEquiv (M := M))]
      exact hq
    exact key F.length le_rfl hq'
  · obtain rfl := Subsingleton.elim F (Coprimary.coprimaryFiltration R M)
    set F := Coprimary.coprimaryFiltration R M
    refine Set.iUnion₂_subset fun i hi q hq ↦ ?_
    have hstep : F i < F (i + 1) := F.strictMonoOn hi.le hi (lt_add_one i)
    have hbot : (⊥ : Submodule R M) < F (i + 1) := bot_le.trans_lt hstep
    have hchain : (Coprimary.payoff R M).A ⟨⊥, F (i + 1), hbot⟩ =
        (Coprimary.payoff R M).A ⟨F i, F (i + 1), hstep⟩ :=
      PayoffFunction.hnFiltration_A_bot_eq_A (μ := Coprimary.payoff R M) (n := i) hstep
    rw [Coprimary.A_payoff, Coprimary.A_payoff] at hchain
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj] at hchain
    have hbotSub : (⊥ : Submodule R M).submoduleOf ⊤ = ⊥ := Submodule.ker_subtype ⊤
    have hmem := Coprimary.associatedPrimes_mono_right hbot le_top
      (Coprimary.min'_mem_associatedPrimes ⟨⊥, F (i + 1), hbot⟩)
    have hmem' : ((Coprimary.associatedPrimes ⟨⊥, F (i + 1), hbot⟩).toFinset.min'
        (Coprimary.associatedPrimes_nonempty _)).asIdeal ∈
          associatedPrimes R (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).submoduleOf ⊤) :=
      hmem
    rw [LinearEquiv.AssociatedPrimes.eq
      ((Submodule.quotEquivOfEqBot _ hbotSub).trans Submodule.topEquiv)] at hmem'
    have hq' := Coprimary.toLinearExtension_eq_min' ⟨F i, F (i + 1), hstep⟩
      (F.piecewise_isCoprimary i hi).existsUnique_associatedPrime
      (p := ⟨q, hq.out.1⟩) hq
    have hgoal : (toLinearExtension (⟨q, hq.out.1⟩ : PrimeSpectrum R)).asIdeal ∈
        associatedPrimes R M := by
      rw [hq', ← hchain]
      exact hmem'
    exact hgoal

end CoprimaryFiltration

end HarderNarasimhan
