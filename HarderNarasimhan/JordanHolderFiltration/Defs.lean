/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.NashEquilibrium.Impl
import HarderNarasimhan.FirstMoverAdvantage.Results
import HarderNarasimhan.SlopeLike.Result
import Mathlib.Order.OrderIsoNat

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

/-
Finite total payoff.
This is the hypothesis that the payoff on the total interval `(⊥, ⊤)` is not `⊤`. It is used to
avoid degenerate situations in the Jordan–Hölder construction where all steps immediately collapse.

API note: this is a standard non-degeneracy hypothesis for the Jordan–Hölder layer.
-/
class FiniteTotalPayoff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  fin_tot_payoff : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤


/-
A strengthened descending chain condition used for Jordan–Hölder filtrations.

Given a strictly decreasing sequence `x`, the condition produces an index `N` such that the
payoff of the step `(x (N+1), x N)` is equal to `⊤`. In the development this is used as a
termination/compactness input to ensure the inductive construction reaches `⊥` in finite time.
-/
class StrongDescendingChainCondition' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wdcc' : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤

open Classical in
@[ext]
/-
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
structure JordanHolderFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
where
  filtration : ℕ → ℒ
  antitone : Antitone filtration
  fin_len : ∃ N : ℕ, filtration N =⊥
  strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i
  first_eq_top : filtration 0 = ⊤
  step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨(filtration (k + 1), filtration k),
    strict_anti k (k+1) (lt_add_one k) hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  step_cond₂ : ∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ <
    μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩

/-
The step relation associated to `μ` for Jordan–Hölder filtrations.
We declare `(x, y)` to be related if `y < x`, the payoff `μ (y, x)` equals the total payoff
`μ (⊥, ⊤)`, and any strict intermediate `z` yields a strictly smaller payoff.

This relation is used to build a `RelSeries` corresponding to a filtration.

API note: use this relation when you want to express a filtration as a `RelSeries`.
-/
def JordanHolderRel {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : SetRel ℒ ℒ :=
{(x, y) | ∃ h : y < x,
    μ ⟨(y, x), h⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  ∧ ∀ z : ℒ, (h' : y < z) → (h'' : z < x) →
    μ ⟨(y, z), h'⟩ < μ ⟨(y , x), h⟩
}

/-
`StrongDescendingChainCondition'` implies the weaker `StrongDescendingChainCondition`.

The primed version produces an index where the payoff equals `⊤`; this is stronger than the
inequality demanded by `StrongDescendingChainCondition`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : StrongDescendingChainCondition' μ] :
StrongDescendingChainCondition μ where
  wdcc := by
    intro f saf
    rcases h.wdcc' f saf with ⟨N, hN⟩
    use N
    exact hN ▸ le_top


/-
`StrongDescendingChainCondition'` is stable under restriction of the slope to an interval.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : StrongDescendingChainCondition' μ]
{I : {p : ℒ × ℒ // p.1 < p.2}} : StrongDescendingChainCondition' (Resμ I μ) where
  wdcc' := fun f saf ↦ h.wdcc' (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ lt_iff_le_not_ge.mpr (saf hn)


/-
Affine property for a slope.

This axiom relates the payoffs of two canonical intervals built from `a` and `b`, expressing a
compatibility of `μ` with lattice operations (`⊓` and `⊔`). It is used to derive convexity.
-/
class Affine {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  affine : ∀ a b : ℒ, (h : ¬ a ≤ b) →
    μ ⟨(a ⊓ b, a), inf_lt_left.2 h⟩ = μ ⟨(b, a ⊔ b), right_lt_sup.2 h⟩

/-
Restriction preserves the affine property.

If `μ` is affine, then its restriction `Resμ I μ` to any interval `I` is affine as well.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] {I : {p : ℒ × ℒ // p.1 < p.2}} :
Affine (Resμ I μ) where
  affine := fun a b h ↦ haff.affine a b h

/-
An affine slope is convex.

This instance packages the standard implication by reducing to the internal convexity predicate
`ConvexI` and then applying the `Affine` axiom.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] : Convex μ := by
  rw [← impl.ConvexI_TotIntvl_iff_Convex]
  refine { convex := ?_ }
  intro x y hx hy hxy
  rw [haff.affine x y hxy]

/-
Restriction preserves finite total payoff under semistability and slope-likeness.

This is used to apply Jordan–Hölder and Harder–Narasimhan results to initial segments of a
filtration.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ]
[hwdcc' : StrongDescendingChainCondition' μ] {x : ℒ} {hx : ⊥ < x} :
FiniteTotalPayoff (Resμ ⟨(⊥, x), hx⟩ μ) := by
  refine { fin_tot_payoff := ?_ }
  simp only [Resμ]
  by_contra h
  have : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
    exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2
      ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
  have := this hst
  simp only [μmax, TotIntvl, ne_eq] at this
  have this_q: μ ⟨(⊥, x), hx⟩ ≤ μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    rw [← this]
    apply le_sSup
    use x, ⟨in_TotIntvl x, Ne.symm <| bot_lt_iff_ne_bot.1 hx⟩
  exact (not_le_of_gt <| h ▸ lt_top_iff_ne_top.2 hftp.fin_tot_payoff) this_q


end HarderNarasimhan
