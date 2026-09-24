/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict

/-!
# Sections 4.1–4.2: first-mover advantage — hypotheses

The chain conditions and weak slope-like conditions from Propositions 4.1 and 4.3.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-! ### The chain conditions and weak slope-like axioms -/

/-- Proposition 4.1 (1). The weak ascending chain condition: every infinite strictly increasing
sequence has an adjacent pair whose payoff is at most the payoff from its left endpoint to
`⊤`. -/
class WeakACC (μ : PayoffFunction ℒ S) : Prop where
  /-- Proposition 4.1 (1): some step payoff is dominated by the tail payoff. -/
  exists_le : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
    ∃ N : ℕ, μ ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩ ≤
      μ ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩

/-- Proposition 4.3 (1). The strong descending chain condition: every infinite strictly decreasing
sequence has an adjacent pair whose payoff is at least the payoff from `⊥` to its larger
endpoint. -/
class StrongDCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Proposition 4.3 (1): some initial payoff is dominated by the step payoff. -/
  exists_le : ∀ x : ℕ → ℒ, (saf : StrictAnti x) →
    ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤
      μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩

/-- Proposition 4.1 (2). For `x < y < ⊤`, at least one of the payoffs on `(x, y)` and `(y, ⊤)` is
at most the payoff on `(x, ⊤)`. -/
class WeakSlopeLikeAtTop (μ : PayoffFunction ℒ S) : Prop where
  /-- Proposition 4.1 (2): the slope-like alternative towards `⊤`. -/
  le_or_le : ∀ z : StrictIntvl ℒ, (hz : z.right < ⊤) →
    μ z ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ ∨
    μ ⟨z.right, ⊤, hz⟩ ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩

/-- Proposition 4.3 (2), in its order-dual formulation. For `⊥ < x < y`, the payoff on `(⊥, y)` is
at most one of the payoffs on `(⊥, x)` and `(x, y)`.

In v1, the first alternative is printed as `μ (⊥, x) ≤ μ (x, y)`. The formal hypothesis
retains the actual dual of Proposition 4.1 (2), namely `μ (⊥, y) ≤ μ (x, y)`, as used by the
paper's duality proof. -/
class WeakSlopeLikeAtBot (μ : PayoffFunction ℒ S) : Prop where
  /-- Proposition 4.3 (2): the order-dual slope-like alternative towards `⊥`. -/
  le_or_le : ∀ z : StrictIntvl ℒ, (hz : ⊥ < z.left) →
    μ ⟨⊥, z.right, lt_trans hz z.lt⟩ ≤ μ z ∨
    μ ⟨⊥, z.right, lt_trans hz z.lt⟩ ≤ μ ⟨⊥, z.left, hz⟩

end PayoffFunction

end HarderNarasimhan
