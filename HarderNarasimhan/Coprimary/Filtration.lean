/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Coprimary.Semistability
public import HarderNarasimhan.Filtration.Unique

/-!
# Existence and uniqueness of coprimary filtrations

Every nonzero finitely generated module over a commutative Noetherian ring has a unique
coprimary filtration, for the fixed linear extension of the prime spectrum. Its successive
quotients have exactly the associated primes of the module.

Existence and uniqueness follow by identifying coprimary filtrations with Harder–Narasimhan
filtrations of the coprimary payoff function.

## Main definitions

* `HarderNarasimhan.Coprimary.coprimaryFiltration`: the coprimary filtration of `M`.

## Main results

* `HarderNarasimhan.PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary`: the
  successive quotients of a Harder–Narasimhan filtration of the coprimary payoff function
  are coprimary.
* `HarderNarasimhan.CoprimaryFiltration.exists_hnFiltration`: every coprimary filtration
  underlies a Harder–Narasimhan filtration of the coprimary payoff function.
* `HarderNarasimhan.CoprimaryFiltration.associatedPrimes_eq_iUnion`: the associated primes
  of `M` are the union of those of the successive quotients of its coprimary filtration.

The `Unique` instance on `HarderNarasimhan.CoprimaryFiltration` expresses existence and
uniqueness; its default element is `HarderNarasimhan.Coprimary.coprimaryFiltration`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- The successive quotients of a Harder–Narasimhan filtration of the coprimary payoff
function are coprimary. -/
lemma PayoffFunction.HarderNarasimhanFiltration.piecewise_isCoprimary
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : (Coprimary.payoff R M).HarderNarasimhanFiltration) :
    ∀ i < F.length, IsCoprimary R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
  intro i hi
  have hstep := F.strictMonoOn hi.le hi (lt_add_one i)
  let := Coprimary.nontrivial_quotient_of_lt hstep
  exact ⟨Coprimary.isSemistable_iff_existsUnique_associatedPrime.mp <|
    (Coprimary.isSemistable_restrict_iff_quotient _ _ hstep).mp
      (F.piecewise_isSemistable i hi)⟩

namespace Coprimary

variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

variable (R M) in
/-- The coprimary filtration of a nonzero finitely generated module over a commutative
Noetherian ring, obtained from the Harder–Narasimhan filtration of its coprimary payoff
function. -/
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
      rw [toLinearExtension_eq_min' ⟨F (n + 1), F (n + 2),
          F.strictMonoOn hn.le hn (lt_add_one (n + 1))⟩
          (F.piecewise_isCoprimary (n + 1) hn).existsUnique_associatedPrime hp,
        toLinearExtension_eq_min' ⟨F n, F (n + 1),
          F.strictMonoOn (Nat.le_of_succ_le hn.le) (Nat.le_of_succ_le hn) (lt_add_one n)⟩
          (F.piecewise_isCoprimary n (Nat.lt_of_succ_lt hn)).existsUnique_associatedPrime hq]
      simpa only [A_payoff, DedekindCut.principal_lt_principal,
        Finset.Colex.singleton_lt_singleton, PayoffFunction.HarderNarasimhanFiltration.toFun_eq_coe]
        using lt_of_not_ge (F.not_A_le_succ n hn) }

/-- The canonical coprimary filtration is the default coprimary filtration. -/
noncomputable instance : Inhabited (CoprimaryFiltration R M) := ⟨coprimaryFiltration R M⟩

instance : Nonempty (CoprimaryFiltration R M) := inferInstance

end Coprimary

namespace CoprimaryFiltration

variable {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Every coprimary filtration has the same underlying chain as a Harder–Narasimhan
filtration of the coprimary payoff function. -/
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
       let := Coprimary.nontrivial_quotient_of_lt hstep
       exact (Coprimary.isSemistable_restrict_iff_quotient _ _ hstep).mpr <|
         Coprimary.isSemistable_iff_existsUnique_associatedPrime.mpr
           (a.piecewise_isCoprimary i hi).existsUnique_associatedPrime
     not_A_le_succ := fun i hi ↦ by
       rw [Coprimary.A_payoff, Coprimary.A_payoff, not_le,
         DedekindCut.principal_lt_principal, Finset.Colex.singleton_lt_singleton]
       exact a.associatedPrime_succ_lt i hi _ _
         (Coprimary.min'_mem_subquotientAssociatedPrimes ⟨a (i + 1), a (i + 2),
           a.strictMonoOn hi.le hi (lt_add_one (i + 1))⟩)
         (Coprimary.min'_mem_subquotientAssociatedPrimes ⟨a i, a (i + 1),
           a.strictMonoOn (Nat.le_of_succ_le hi.le) (Nat.le_of_succ_le hi)
             (lt_add_one i)⟩) }, rfl⟩

/-- Every coprimary filtration has the same underlying chain as the canonical
Harder–Narasimhan filtration of the coprimary payoff function. -/
private lemma coe_eq_hnFiltration (a : CoprimaryFiltration R M) :
    ⇑a = ⇑((Coprimary.payoff R M).hnFiltration) := by
  obtain ⟨F, hF⟩ := exists_hnFiltration a
  rw [hF, Subsingleton.elim F ((Coprimary.payoff R M).hnFiltration)]

/-- A nonzero finitely generated module over a commutative Noetherian ring has a unique
coprimary filtration for the fixed linear extension of the prime spectrum. -/
@[no_expose]
noncomputable instance : Unique (CoprimaryFiltration R M) where
  uniq a := by
    ext n
    rw [coe_eq_hnFiltration a, coe_eq_hnFiltration default]

/-- The associated primes of a module are the union of the associated primes of the
successive quotients of its coprimary filtration. -/
theorem associatedPrimes_eq_iUnion (F : CoprimaryFiltration R M) :
    associatedPrimes R M =
      ⋃ i < F.length, associatedPrimes R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
  apply subset_antisymm
  · -- Dévissage along the chain places every associated prime in one of its factors.
    have key : ∀ k, k ≤ F.length →
        associatedPrimes R ↥(F k) ⊆
          ⋃ i < F.length, associatedPrimes R (F (i + 1) ⧸ (F i).submoduleOf (F (i + 1))) := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [show F 0 = ⊥ from F.head_eq_bot, associatedPrimes.eq_empty_of_subsingleton]
        exact Set.empty_subset _
      | succ k ih =>
        intro hk q hq
        rcases associatedPrimes.subset_union_of_exact
          (Submodule.injective_subtype ((F k).submoduleOf (F (k + 1))))
          (LinearMap.exact_subtype_mkQ ((F k).submoduleOf (F (k + 1)))) hq with h | h
        · apply ih ((Nat.le_succ k).trans hk)
          have hAss : associatedPrimes R ↥((F k).submoduleOf (F (k + 1))) =
              associatedPrimes R ↥(F k) :=
            LinearEquiv.AssociatedPrimes.eq
              (Submodule.comapSubtypeEquivOfLe (F.monotone (Nat.le_succ k)))
          exact hAss ▸ h
        · exact Set.mem_iUnion₂.mpr ⟨k, Nat.lt_of_succ_le hk, h⟩
    intro q hq
    apply key F.length le_rfl
    rwa [show F F.length = ⊤ from F.length_eq_top,
      LinearEquiv.AssociatedPrimes.eq (Submodule.topEquiv (M := M))]
  · -- For the canonical chain, each factor prime is also the prime of an initial segment.
    obtain rfl := Subsingleton.elim F (Coprimary.coprimaryFiltration R M)
    set F := Coprimary.coprimaryFiltration R M
    refine Set.iUnion₂_subset fun i hi q hq ↦ ?_
    have hstep : F i < F (i + 1) := F.strictMonoOn hi.le hi (lt_add_one i)
    have hbot : (⊥ : Submodule R M) < F (i + 1) := bot_le.trans_lt hstep
    have hchain : (Coprimary.payoff R M).A ⟨⊥, F (i + 1), hbot⟩ =
        (Coprimary.payoff R M).A ⟨F i, F (i + 1), hstep⟩ :=
      PayoffFunction.hnFiltration_A_bot_eq_A (μ := Coprimary.payoff R M) (n := i) hstep
    rw [Coprimary.A_payoff, Coprimary.A_payoff] at hchain
    simp only [DedekindCut.principal_inj, toColex_inj, Finset.singleton_inj] at hchain
    change (toLinearExtension (⟨q, hq.out.1⟩ : PrimeSpectrum R)).asIdeal ∈ associatedPrimes R M
    rw [Coprimary.toLinearExtension_eq_min' ⟨F i, F (i + 1), hstep⟩
      (F.piecewise_isCoprimary i hi).existsUnique_associatedPrime hq, ← hchain]
    -- Include that initial segment into `M`, using `⊤ / ⊥ ≃ M`.
    rw [← LinearEquiv.AssociatedPrimes.eq
      ((Submodule.quotEquivOfEqBot _ (Submodule.ker_subtype (⊤ : Submodule R M))).trans
        Submodule.topEquiv)]
    exact Coprimary.subquotientAssociatedPrimes_mono_right hbot le_top
      (Coprimary.min'_mem_subquotientAssociatedPrimes ⟨⊥, F (i + 1), hbot⟩)

end CoprimaryFiltration

end HarderNarasimhan
