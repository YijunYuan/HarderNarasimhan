/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.NashEquilibrium.Impl
import HarderNarasimhan.FirstMoverAdvantage.Results
import HarderNarasimhan.PayoffFunction.SlopeLike
import HarderNarasimhan.PayoffFunction.Convex
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Rel

/-!
# Jordan–Hölder filtrations: definitions

This file introduces the abstract notion of a Jordan–Hölder filtration associated to a slope
function `μ`. Conceptually, a Jordan–Hölder filtration is a finite strictly decreasing chain
starting at `⊤` and ending at `⊥` whose successive steps have constant payoff (equal to the
total payoff `μ (⊥, ⊤)`), and are “stable” in the sense that any intermediate refinement yields a
strictly smaller payoff.

The surrounding theory (in `JordanHolderFiltration/Impl.lean` and the results file) shows how to
construct such filtrations under slope-like, semistability, and chain-condition hypotheses.

API overview:

* Import this file to use the core typeclasses `FiniteTotalPayoff` and
  `StrongDescendingChainCondition'`, and the main structure `JordanHolderFiltration`.
* The relation `JordanHolderRel` is the standard bridge to `Mathlib.Order.RelSeries`.
* Prefer importing `HarderNarasimhan.JordanHolderFiltration.Results` for existence theorems and
  length/stability results.
-/

namespace HarderNarasimhan

/--
Finite total payoff.
This is the hypothesis that the payoff on the total interval `(⊥, ⊤)` is not `⊤`. It is used to
avoid degenerate situations in the Jordan–Hölder construction where all steps immediately collapse.

API note: this is a standard non-degeneracy hypothesis for the Jordan–Hölder layer.
-/
class FiniteTotalPayoff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : Prop where
  fin_tot_payoff : μ ⊤ ≠ ⊤


/--
A strengthened descending chain condition used for Jordan–Hölder filtrations.

Given a strictly decreasing sequence `x`, the condition produces an index `N` such that the
payoff of the step `(x (N+1), x N)` is equal to `⊤`. In the development this is used as a
termination/compactness input to ensure the inductive construction reaches `⊥` in finite time.
-/
class StrongDescendingChainCondition' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : Prop where
  sdcc' : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨x (N +1), x N, sax <| lt_add_one N⟩ = ⊤

open Classical in
/--
`JordanHolderFiltration μ` is a finite strictly decreasing chain in `ℒ` with stable steps.
Fields:
- `filtration` is the chain `ℕ → ℒ`.
- `antitone` and `strict_anti` state monotonicity and strict decrease on the initial segment.
- `fin_len` gives a finite length where the chain reaches `⊥`.
- `first_eq_top` normalizes the chain to start at `⊤`.
- `step_cond₁` fixes the payoff of each step to be the total payoff `μ (⊥, ⊤)`.
- `step_cond₂` is the stability condition: any intermediate refinement yields strictly smaller
  payoff.

API note: this structure is the central object of the Jordan–Hölder layer.
-/
@[ext]
structure JordanHolderFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S)
where
  filtration : ℕ → ℒ
  antitone : Antitone filtration
  fin_len : ∃ N : ℕ, filtration N = ⊥
  strict_anti : StrictAntiOn filtration (Set.Iic (Nat.find fin_len))
  first_eq_top : filtration 0 = ⊤
  step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨filtration (k + 1), filtration k,
    strict_anti hk.le hk (lt_add_one k)⟩ = μ ⊤
  step_cond₂ : ∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨filtration (i+1), z, h'⟩ <
    μ ⟨filtration (i+1), filtration i, strict_anti hi.le hi (lt_add_one i)⟩

namespace JordanHolderFiltration

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S] {μ : PayoffFunction ℒ S}

open Classical in
/--
The length of a Jordan–Hölder filtration: the first index at which it reaches `⊥`.

All `Nat.find`-based bookkeeping about the chain length is encapsulated here and in the
accompanying lemmas; downstream code should use `F.length` and never touch `Nat.find` directly.
-/
noncomputable def length (F : JordanHolderFiltration μ) : ℕ := Nat.find F.fin_len

open Classical in
@[simp] lemma filtration_length (F : JordanHolderFiltration μ) :
    F.filtration F.length = ⊥ := Nat.find_spec F.fin_len

open Classical in
lemma ne_bot_of_lt_length (F : JordanHolderFiltration μ) {m : ℕ} (h : m < F.length) :
    F.filtration m ≠ ⊥ := Nat.find_min F.fin_len h

open Classical in
lemma length_le_of_eq_bot (F : JordanHolderFiltration μ) {m : ℕ}
    (h : F.filtration m = ⊥) : F.length ≤ m := Nat.find_min' F.fin_len h

end JordanHolderFiltration

/--
The step relation associated to `μ` for Jordan–Hölder filtrations.
We declare `(x, y)` to be related if `y < x`, the payoff `μ (y, x)` equals the total payoff
`μ (⊥, ⊤)`, and any strict intermediate `z` yields a strictly smaller payoff.

This relation is used to build a `RelSeries` corresponding to a filtration.

API note: use this relation when you want to express a filtration as a `RelSeries`.
-/
def JordanHolderRel {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
{(x, y) | ∃ h : y < x,
    μ ⟨y, x, h⟩ = μ ⊤
  ∧ ∀ z : ℒ, (h' : y < z) → (h'' : z < x) →
    μ ⟨y, z, h'⟩ < μ ⟨y, x, h⟩
}

/--
`StrongDescendingChainCondition'` implies the weaker `StrongDescendingChainCondition`.

The primed version produces an index where the payoff equals `⊤`; this is stronger than the
inequality demanded by `StrongDescendingChainCondition`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S} [h : StrongDescendingChainCondition' μ] :
StrongDescendingChainCondition μ where
  wdcc := fun f saf ↦ let ⟨N, hN⟩ := h.sdcc' f saf; ⟨N, hN ▸ le_top⟩


/--
`StrongDescendingChainCondition'` is stable under restriction of the slope to an interval.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S} [h : StrongDescendingChainCondition' μ]
{I : StrictIntvl ℒ} : StrongDescendingChainCondition' (Resμ I μ) where
  sdcc' := fun f saf ↦ h.sdcc' (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ saf hn


/--
Restriction preserves the affine property (transitional `Resμ`-keyed copy of the
`PayoffFunction.restrict` instance, so that instance search fires on `Resμ`).
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : PayoffFunction ℒ S} [haff : μ.IsAffine] {I : StrictIntvl ℒ} :
(Resμ I μ).IsAffine where
  eq := fun a b h ↦ haff.eq a b h

/--
Restriction preserves finite total payoff under semistability and slope-likeness.

This is used to apply Jordan–Hölder and Harder–Narasimhan results to initial segments of a
filtration.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : PayoffFunction ℒ S}
[hftp : FiniteTotalPayoff μ] [hsl : μ.IsSlopeLike] [hst : μ.IsSemistable]
[hsdcc' : StrongDescendingChainCondition' μ] {x : ℒ} {hx : ⊥ < x} :
FiniteTotalPayoff (Resμ ⟨⊥, x, hx⟩ μ) := by
  refine { fin_tot_payoff := ?_ }
  simp only [Resμ]
  by_contra h
  have : μ.IsSemistable → μmax μ ⊤ = μ ⊤ :=
    fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2
      ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
  have := this hst
  have this_q : μ ⟨⊥, x, hx⟩ ≤ μ ⊤ := this ▸ le_iSup₂_of_le x ⟨hx, le_top⟩ le_rfl
  exact (not_le_of_gt <| h ▸ lt_top_iff_ne_top.2 hftp.fin_tot_payoff) this_q


end HarderNarasimhan
