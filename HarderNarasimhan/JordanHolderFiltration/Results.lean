/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.JordanHolderFiltration.Impl

/-!
# Jordan–Hölder filtrations: public results

This file provides the public-facing statements for Jordan–Hölder filtrations.

In particular, it gives existence of a `JordanHolderFiltration μ` under the usual hypotheses,
constructs an associated `RelSeries`, and proves auxiliary results about stability and the
length of filtrations.

The proofs are implemented in `HarderNarasimhan.JordanHolderFiltration.Impl`.

API overview:

* Import this file (rather than `...Impl`) when using Jordan–Hölder filtrations as an abstract
  tool.
* The main entry point is the `Nonempty (JordanHolderFiltration μ)` instance under the standard
  hypotheses.
-/

namespace HarderNarasimhan

/- Theorem 4.25. -/
open Classical in
/--
Existence of a Jordan–Hölder filtration (Theorem 4.25).
Under finite total payoff, slope-likeness, semistability, and the strengthened descending chain
condition, we construct a nonempty type of Jordan–Hölder filtrations for `μ`.

API note: this instance is the main entry point for “there exists a JH filtration”.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ]
[hst : Semistable μ] [hwdcc' : StrongDescendingChainCondition' μ] :
Nonempty (JordanHolderFiltration μ)
:= Nonempty.intro {
  filtration := impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc',
  antitone := fun x y hxy ↦
    if hy : y ≤ Nat.find (impl.JHFil_fin_len μ FiniteTotalPayoff.fin_tot_payoff hsl hst
      StrongDescendingChainCondition'.wdcc') then
      (Nat.le_induction
        (fun a ↦ le_rfl)
        (fun n hn hind hn' ↦
          le_trans (le_of_lt <| impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <|
            bot_lt_iff_ne_bot.2 <|
              Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <|
            hind <| le_trans (le_of_lt <| lt_add_one n) hn')
        : ∀ y : ℕ, x ≤ y →
          y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') →
            impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y ≤
              impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x
      ) y hxy hy
    else
      (Nat.le_induction
        (Nat.find_spec (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc'))
        fun i hi hi' ↦ by simp only [impl.JHFil, hi']; simp only [not_lt_bot, false_and,
          exists_false, Set.setOf_false, Set.not_nonempty_empty, ↓reduceDIte]
        : ∀ n : ℕ, Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') ≤ n →
          impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n = ⊥)
      y (le_of_lt <| lt_of_not_ge hy) ▸ bot_le,
  fin_len := impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc',
  strict_anti := fun x y hxy hx' ↦
    (Nat.le_induction
      (fun a ↦ impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x <|
        bot_lt_iff_ne_bot.2 <|
          Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') <|
            lt_of_lt_of_le (lt_add_one x) a)
      (fun n hn hind hn' ↦
        lt_trans (impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <|
          bot_lt_iff_ne_bot.2 <|
            Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <|
              hind (le_trans (le_of_lt <| lt_add_one n) hn'))
        : ∀ y : ℕ, (x+1) ≤ y →
          y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') →
            impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y <
              impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x
    ) y hxy hx',
  first_eq_top := of_eq_true (eq_self ⊤),
  step_cond₁ := fun k hk ↦
    impl.JHFil_prop₁ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' k <|
      bot_lt_iff_ne_bot.2 <|
        (Nat.find_min <| impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hk,
  step_cond₂ := fun i hi z h' h'' ↦
    impl.JHFil_prop₂ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' i
      (bot_lt_iff_ne_bot.2 <| Nat.find_min
        (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hi) z h' h''
}

open Classical in
/--
Construct a Jordan–Hölder `RelSeries` from an existing filtration.
Given the existence instance for `JordanHolderFiltration μ`, we build a `RelSeries` for the
relation `JordanHolderRel μ` whose head is `⊤` and whose last element is `⊥`.

API note: this is the `RelSeries`-shaped entry point corresponding to the existence instance.
-/
theorem exists_JordanHolderSeries
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ]
[hst : Semistable μ] [hwdcc' : StrongDescendingChainCondition' μ] :
∃ s : RelSeries (JordanHolderRel μ), s.head = ⊤ ∧ s.last = ⊥
:= by
  have := (inferInstance : Nonempty (JordanHolderFiltration μ)).some
  let JH : RelSeries (JordanHolderRel μ) := {
    length := Nat.find this.fin_len,
    toFun := fun n ↦ this.filtration n.toNat,
    step := by
      intro n
      use this.strict_anti n n.succ (Nat.lt_add_one ↑n) (Fin.is_le n.succ)
      exact ⟨this.step_cond₁ n n.isLt,this.step_cond₂ n n.isLt⟩
  }
  exact ⟨JH, ⟨this.first_eq_top, Nat.find_spec this.fin_len⟩⟩

open Classical in
/--
Reformulate the stability condition as piecewise `Stable` for restricted slopes.

This lemma bridges the `step_cond₂` field of `JordanHolderFiltration` with the `Stable` predicate
for the restricted slope on each step.
-/
theorem piecewise_stable_iff
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N = ⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i) :
(
∀ i : ℕ, (hi : i < Nat.find fin_len) →
  Stable (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
)
↔ (∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ <
    μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩)
:= by
  constructor
  · exact fun a i hi z h' h'' ↦
    impl.step_cond₂_of_stable μ filtration fin_len strict_anti a i hi z h' h''
  · exact fun a i hi ↦ impl.stable_of_step_cond₂ μ filtration fin_len strict_anti a i hi

open Classical in
/--
Lengths of Jordan–Hölder filtrations agree under modularity.

Assuming `ℒ` is modular and `μ` satisfies the standard hypotheses (including affinity), any two
Jordan–Hölder filtrations for `μ` have the same finite length.
-/
theorem length_eq_of_JordanHolderFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [IsModularLattice ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ]
[StrongDescendingChainCondition' μ] [Affine μ] :
∀ JH1 JH2 : JordanHolderFiltration μ, Nat.find JH1.fin_len = Nat.find JH2.fin_len
:= fun JH1 JH2 ↦ eq_of_le_of_ge (impl.induction_on_length_of_JordanHolderFiltration
  (Nat.find JH2.fin_len) ℒ _ _ _ inferInstance inferInstance _ _ μ inferInstance inferInstance
  inferInstance inferInstance inferInstance ⟨JH2,rfl.le⟩ JH1) <|
  impl.induction_on_length_of_JordanHolderFiltration (Nat.find JH1.fin_len) ℒ _ _ _ inferInstance
  inferInstance _ _ _ inferInstance inferInstance inferInstance inferInstance inferInstance
  ⟨JH1,rfl.le⟩ JH2


end HarderNarasimhan
