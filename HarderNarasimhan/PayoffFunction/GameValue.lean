/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.SlopeLike
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.OrderIsoNat

/-!
# The values of the Harder–Narasimhan Games

This file computes the two global values of the Harder–Narasimhan Games: the first-player
value `μ.A ⊤` and the second-player value `μ.B ⊤` (often denoted `μ_A^*` and `μ_B^*`).

Under a weak ascending chain condition and a slope-like alternative towards `⊤`, player A's
value collapses to `μ.min ⊤` (`A_top_eq_min_top`); dually, under a strong descending chain
condition and the alternative towards `⊥`, player B's value collapses to `μ.max ⊤`
(`B_top_eq_max_top`).  In both situations the *first-mover advantage* `μ.A ⊤ ≤ μ.B ⊤`
follows.

## Main definitions

* `PayoffFunction.WeakACC`, `PayoffFunction.StrongDCC` : the weak ascending and strong
  descending chain conditions.
* `PayoffFunction.WeakSlopeLikeAtTop`, `PayoffFunction.WeakSlopeLikeAtBot` : the two
  weakenings of `IsSlopeLike` anchored at `⊤` resp. `⊥`.

## Main results

* `A_top_eq_min_top`, `A_top_le_B_top` : player A's value collapses to `μ.min ⊤`, and the
  first-mover advantage follows.
* `B_top_eq_max_top`, `A_top_le_B_top_of_strongDCC` : player B's value collapses to
  `μ.max ⊤`, and the first-mover advantage follows.
* `A_top_dual`, `B_top_dual` : order duality exchanges the two game values.
* `strongDCC_of_wellOrderedRank` : a well-ordered rank function yields `StrongDCC`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-! ### The chain conditions and weak slope-like axioms -/

/-- The *weak ascending chain condition* (`WeakACC`): along any strictly increasing chain
there is a step whose payoff is bounded by the payoff of the corresponding tail interval.
This is the hypothesis controlling player A's forward moves. -/
class WeakACC (μ : PayoffFunction ℒ S) : Prop where
  /-- Some step payoff is dominated by the tail payoff. -/
  exists_le : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
    ∃ N : ℕ, μ ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩ ≤
      μ ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩

/-- In a well-founded order there are no strictly increasing chains, so `WeakACC` holds
trivially. -/
instance {μ : PayoffFunction ℒ S} [WellFoundedGT ℒ] : μ.WeakACC :=
  ⟨fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf)⟩

/-- The *strong descending chain condition* (`StrongDCC`): along any strictly decreasing
chain there is a step whose payoff dominates the payoff of the corresponding initial
interval.  This is the dual hypothesis controlling player B's backward moves. -/
class StrongDCC (μ : PayoffFunction ℒ S) : Prop where
  /-- Some initial payoff is dominated by the step payoff. -/
  exists_le : ∀ x : ℕ → ℒ, (saf : StrictAnti x) →
    ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤
      μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩

/-- The weakening of `IsSlopeLike` anchored at `⊤`, used to compute player A's value. -/
class WeakSlopeLikeAtTop (μ : PayoffFunction ℒ S) : Prop where
  /-- The slope-like alternative towards `⊤`. -/
  le_or_le : ∀ z : StrictIntvl ℒ, (hz : z.right < ⊤) →
    μ z ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩ ∨
    μ ⟨z.right, ⊤, hz⟩ ≤ μ ⟨z.left, ⊤, lt_trans z.lt hz⟩

/-- The weakening of `IsSlopeLike` anchored at `⊥`, used to compute player B's value. -/
class WeakSlopeLikeAtBot (μ : PayoffFunction ℒ S) : Prop where
  /-- The slope-like alternative towards `⊥`. -/
  le_or_le : ∀ z : StrictIntvl ℒ, (hz : ⊥ < z.left) →
    μ ⟨⊥, z.right, lt_trans hz z.lt⟩ ≤ μ z ∨
    μ ⟨⊥, z.right, lt_trans hz z.lt⟩ ≤ μ ⟨⊥, z.left, hz⟩

section LinearOrder

variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- Over a linear order, a slope-like payoff function satisfies the weakening at `⊤`. -/
instance [hμ : μ.IsSlopeLike] : μ.WeakSlopeLikeAtTop :=
  ⟨fun z hz ↦ (hμ.slopelike z.left z.right ⊤ ⟨z.lt, hz⟩).1.imp id le_of_lt⟩

/-- Over a linear order, a slope-like payoff function satisfies the weakening at `⊥`. -/
instance [hμ : μ.IsSlopeLike] : μ.WeakSlopeLikeAtBot :=
  ⟨fun z hz ↦ (hμ.slopelike ⊥ z.left z.right ⟨hz, z.lt⟩).2.2.1.elim (Or.inr ∘ le_of_lt) Or.inl⟩

end LinearOrder

/-! ### Player A's value -/

variable {μ : PayoffFunction ℒ S}

/-- The set of “bad” first moves for player A: elements `YA < ⊤` such that every `xA < ⊤`
admits a follow-up `xB` whose payoff is not bounded by `μ (YA, ⊤)`.  The computation of
player A's value proceeds by showing this set is empty. -/
private def badSet (μ : PayoffFunction ℒ S) : Set ℒ :=
  {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬ μ ⟨xA, xB, hAB⟩ ≤ μ ⟨YA, ⊤, h⟩}

/-- The auxiliary strictly increasing sequence of bad first moves used in the contradiction
argument for `A_top_eq_min_top`. -/
private noncomputable def badSeq (μ : PayoffFunction ℒ S) [h₂ : μ.WeakSlopeLikeAtTop]
    (h₃ : (badSet μ).Nonempty) (k : ℕ) : badSet μ :=
  match k with
  | 0 => ⟨h₃.choose, h₃.choose_spec⟩
  | k + 1 => by
    let next := (badSeq μ h₃ k).prop.out.choose_spec
      (badSeq μ h₃ k) (badSeq μ h₃ k).prop.out.choose
    have h''' := next.choose_spec.choose_spec
    have h' : next.choose < ⊤ := lt_top_iff_ne_top.2 fun hcon ↦
      h''' (le_of_eq <| congrArg μ <| StrictIntvl.ext rfl hcon)
    have hle := (h₂.le_or_le ⟨badSeq μ h₃ k, next.choose,
      next.choose_spec.choose⟩ h').resolve_left h'''
    refine ⟨next.choose, h', fun xA hxA ↦ ?_⟩
    obtain ⟨xB, hAB, con⟩ := (badSeq μ h₃ k).prop.out.choose_spec xA hxA
    exact ⟨xB, hAB, fun hcon ↦ con (hcon.trans hle)⟩

private lemma iInf_top_eq_min_top (μ : PayoffFunction ℒ S) :
    ⨅ (x : ℒ) (hx : x < ⊤), μ ⟨x, ⊤, hx⟩ = μ.min ⊤ :=
  le_antisymm (le_iInf₂ fun u hu ↦ iInf₂_le u hu.2)
    (le_iInf₂ fun x hx ↦ iInf₂_le x ⟨bot_le, hx⟩)

/-- Player A's value is the global minimum: under the weak ascending chain condition and the
weak slope-like alternative at `⊤`, the first-player value `μ.A ⊤` equals `μ.min ⊤`. -/
theorem A_top_eq_min_top [h₁ : μ.WeakACC] [h₂ : μ.WeakSlopeLikeAtTop] :
    μ.A ⊤ = μ.min ⊤ := by
  rw [← iInf_top_eq_min_top]
  have key : ∀ yA : ℒ, (hyA : yA < ⊤) → ∃ xA : ℒ, xA < ⊤ ∧ (∀ xB : ℒ, (hAB : xA < xB) →
      μ ⟨xA, xB, hAB⟩ ≤ μ ⟨yA, ⊤, hyA⟩) := by
    by_contra!
    let Y := badSeq μ this
    have hsmf : StrictMono (fun n ↦ (Y n : ℒ)) := strictMono_nat_of_lt_succ fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose
    have hfinal : ∀ n : ℕ, ¬ μ ⟨Y n, Y (n+1), hsmf (Nat.lt_add_one n)⟩ ≤
        μ ⟨Y n, ⊤, lt_of_lt_of_le (hsmf (Nat.lt_add_one n)) le_top⟩ := fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose_spec
    obtain ⟨N, hN⟩ := h₁.exists_le (fun n ↦ Y n) hsmf
    exact hfinal N hN
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun yA hyA ↦ ?_
    obtain ⟨xA, hxA, h'⟩ := key yA hyA
    exact iInf₂_le_of_le xA ⟨bot_le, hxA⟩ (iSup₂_le fun xB hxB ↦ h' xB hxB.1)
  · exact le_iInf₂ fun x hx ↦ iInf₂_le_of_le x hx.2
      (le_iSup₂_of_le ⊤ ⟨hx.2, le_rfl⟩ le_rfl)

/-- The first-mover advantage `μ.A ⊤ ≤ μ.B ⊤`, under the hypotheses computing player A's
value. -/
theorem A_top_le_B_top [μ.WeakACC] [μ.WeakSlopeLikeAtTop] : μ.A ⊤ ≤ μ.B ⊤ :=
  A_top_eq_min_top.trans_le <| le_iSup₂_of_le ⊤ ⟨bot_lt_top, le_rfl⟩ le_rfl

/-! ### Duality and player B's value -/

/-- `StrongDCC` for `μ` gives `WeakACC` for the dual payoff function. -/
instance [h₁ : μ.StrongDCC] : μ.dual.WeakACC :=
  ⟨fun xd smf ↦ h₁.exists_le (fun n ↦ (xd n).ofDual) fun _ _ hab ↦ smf hab⟩

/-- `WeakSlopeLikeAtBot` for `μ` gives `WeakSlopeLikeAtTop` for the dual payoff function. -/
instance [h₂ : μ.WeakSlopeLikeAtBot] : μ.dual.WeakSlopeLikeAtTop :=
  ⟨fun z hz ↦ h₂.le_or_le ⟨z.right, z.left, z.lt⟩ hz⟩

/-- Duality exchanges the game values: player A's value of `μ.dual` is player B's value of
`μ`. -/
theorem A_top_dual : OrderDual.ofDual (μ.dual.A ⊤) = μ.B ⊤ :=
  le_antisymm
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le (OrderDual.ofDual a) ⟨ha.2, ha.1⟩
      (le_iInf₂ fun b hb ↦ iInf₂_le b ⟨hb.2, hb.1⟩))
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le (OrderDual.toDual a) ⟨ha.2, ha.1⟩
      (le_iInf₂ fun b hb ↦ iInf₂_le b ⟨hb.2, hb.1⟩))

/-- Duality exchanges the game values: player B's value of `μ.dual` is player A's value of
`μ`. -/
theorem B_top_dual : OrderDual.ofDual (μ.dual.B ⊤) = μ.A ⊤ :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le (OrderDual.toDual a) ⟨ha.2, ha.1⟩
      (iSup₂_le fun b hb ↦ le_iSup₂_of_le b ⟨hb.2, hb.1⟩ le_rfl))
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le (OrderDual.ofDual a) ⟨ha.2, ha.1⟩
      (iSup₂_le fun b hb ↦ le_iSup₂_of_le b ⟨hb.2, hb.1⟩ le_rfl))

private lemma iSup_bot_eq_max_top (μ : PayoffFunction ℒ S) :
    ⨆ (y : ℒ) (hy : ⊥ < y), μ ⟨⊥, y, hy⟩ = μ.max ⊤ :=
  le_antisymm (iSup₂_le fun y hy ↦ le_iSup₂_of_le y ⟨hy, le_top⟩ le_rfl)
    (iSup₂_le fun y hy ↦ le_iSup₂_of_le y hy.1 le_rfl)

/-- Player B's value is the global maximum: under the strong descending chain condition and
the weak slope-like alternative at `⊥`, the second-player value `μ.B ⊤` equals `μ.max ⊤`. -/
theorem B_top_eq_max_top [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] : μ.B ⊤ = μ.max ⊤ := by
  have := A_top_eq_min_top (μ := μ.dual)
  rw [← iInf_top_eq_min_top] at this
  rw [← iSup_bot_eq_max_top, ← A_top_dual, this]
  rfl

/-- The first-mover advantage `μ.A ⊤ ≤ μ.B ⊤`, under the hypotheses computing player B's
value. -/
theorem A_top_le_B_top_of_strongDCC [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] : μ.A ⊤ ≤ μ.B ⊤ := by
  have h := A_top_le_B_top (μ := μ.dual)
  rw [← A_top_dual, ← B_top_dual]
  exact h

omit [Nontrivial ℒ] in
/-- A monotone real-valued rank function with well-ordered range yields the strong
descending chain condition, provided `μ` is `⊤` on rank-constant intervals. -/
theorem strongDCC_of_wellOrderedRank (μ : PayoffFunction ℒ S)
    (r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
    (h : ∀ z : StrictIntvl ℒ, r z.left = r z.right → μ z = ⊤) :
    μ.StrongDCC := by
  refine ⟨fun x saf ↦ ?_⟩
  obtain ⟨m, hmW, hmin⟩ := hr₂.wf.has_min {s : Set.range r | ∃ N : ℕ, s = r (x N)}
    ⟨⟨r (x 0), Set.mem_range_self (x 0)⟩, 0, rfl⟩
  obtain ⟨n, hn⟩ := hmW
  have heq : r (x n) = r (x (n + 1)) :=
    eq_of_le_of_not_lt' (hr₁ (saf (Nat.lt_add_one n)).le)
      (hn ▸ hmin ⟨r (x (n + 1)), Set.mem_range_self (x (n + 1))⟩ ⟨n + 1, rfl⟩)
  exact ⟨n, (h ⟨x (n + 1), x n, saf (Nat.lt_add_one n)⟩ heq.symm) ▸ le_top⟩

section SlopeLike

variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

omit [Nontrivial ℒ] [BoundedOrder ℒ] in
/-- For a slope-like payoff function over a well-founded order, the first-player value of any
interval is the minimum payoff.  This is the interval version of `A_top_eq_min_top`, obtained
by restricting `μ` to the interval. -/
lemma IsSlopeLike.min_eq_A [WellFoundedGT ℒ] (hsl : μ.IsSlopeLike) (I : StrictIntvl ℒ) :
    μ.min I = μ.A I := by
  have h := A_top_eq_min_top (μ := μ.restrict I)
  rw [A_restrict_apply, min_restrict_apply, StrictIntvl.ofSub_top] at h
  exact h.symm

end SlopeLike

end PayoffFunction

end HarderNarasimhan
