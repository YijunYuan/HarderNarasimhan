import HarderNarasimhan.FirstMoverAdvantage.Impl
import HarderNarasimhan.SlopeLike.Defs
import Mathlib.Order.OrderIsoNat

/-!
# First-mover advantage: abstract hypotheses

This file packages the abstract order-theoretic hypotheses used in the "first-mover advantage"
arguments (Section 4 in the accompanying development).

We define chain conditions and weakened versions of the `SlopeLike` axiom that are tailored to
inequalities involving the game-theoretic values `μAstar` and `μBstar`.

API overview:

* Import this file to access the hypothesis typeclasses used throughout the game-theoretic layer
  (e.g. `WeakAscendingChainCondition`, `StrongDescendingChainCondition`, `WeakSlopeLike₁`,
  `WeakSlopeLike₂`).
* For the main theorems relating `μAstar`/`μBstar` to `μmin`/`μmax`, import
  `HarderNarasimhan.FirstMoverAdvantage.Results`.
-/

namespace HarderNarasimhan

/-
Weak ascending chain condition.
Given a strictly increasing sequence `x : ℕ → ℒ`, this asserts existence of an index `N` where the
payoff of the step `(x N, x (N+1))` is bounded above by the payoff of the interval `(x N, ⊤)`.

This is the hypothesis used to control player A's "forward" moves.

API note: this is one of the standard hypothesis packages used to compute `μAstar`.
-/
class WeakAscendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wacc : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
    ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤
      μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩

/-
In a well-founded partial order, strictly increasing sequences do not exist.

Consequently, `WeakAscendingChainCondition μ` holds trivially.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} : WeakAscendingChainCondition μ :=
{wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))}


/-
Strong descending chain condition.
Given a strictly decreasing sequence `x : ℕ → ℒ`, this asserts existence of an index `N` where the
payoff of the "initial" interval `(⊥, x N)` is bounded above by the payoff of the step
`(x (N+1), x N)`.

This is the hypothesis used to control player B's "backward" moves.

API note: this is the dual hypothesis package used to compute `μBstar`.
-/
class StrongDescendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wdcc : ∀ x : ℕ → ℒ, (saf : StrictAnti x) →
    ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤
      μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩


/-
First weak slope-like axiom.
This is the disjunctive inequality obtained from `SlopeLike` by specializing to the top element.
It is used in the proof of Proposition 4.1 (first-mover advantage for player A).

API note: this is a weakening of `SlopeLike` tailored to the first-mover advantage proofs.
-/
class WeakSlopeLike₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wsl₁ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) →
    μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨
    μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩


/-
Second weak slope-like axiom.
This is the disjunctive inequality obtained from `SlopeLike` by specializing to the bottom
element. It is used in the proof of Proposition 4.3 (first-mover advantage for player B).

API note: this is the dual weakening of `SlopeLike`, used for player B.
-/
class WeakSlopeLike₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wsl₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) →
    μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨
    μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩

/-
`SlopeLike` implies `WeakSlopeLike₁` when the codomain is linearly ordered.

This instance extracts the relevant disjunction by applying the `SlopeLike` axiom with `c = ⊤`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : SlopeLike μ] :
WeakSlopeLike₁ μ := by
  refine { wsl₁ := fun z hz ↦ ?_ }
  rcases (hμ.slopelike z.val.1 z.val.2 ⊤ ⟨z.prop,hz⟩).1 with this | this
  · exact Or.inl this
  · exact Or.inr <| le_of_lt this

/-
`SlopeLike` implies `WeakSlopeLike₂` when the codomain is linearly ordered.

This instance extracts the relevant disjunction by applying the `SlopeLike` axiom with `a = ⊥`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : SlopeLike μ] :
WeakSlopeLike₂ μ := by
  refine { wsl₂ := fun z hz ↦ ?_ }
  rcases (hμ.slopelike ⊥ z.val.1 z.val.2 ⟨hz,z.prop⟩).2.2.1 with this | this
  · exact Or.inr <| le_of_lt this
  · exact Or.inl this


end HarderNarasimhan
