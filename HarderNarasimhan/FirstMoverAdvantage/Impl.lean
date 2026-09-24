/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.FirstMoverAdvantage.Defs
public import HarderNarasimhan.SlopeLike.Impl
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.OrderIsoNat

/-!
# Sections 4.1–4.2: first-mover advantage — proofs

Proofs of Propositions 4.1 and 4.3, duality, and the chain-condition criteria
of Remarks 4.2 and 4.4.
-/

@[expose] public section

namespace HarderNarasimhan.Impl

open _root_.HarderNarasimhan.PayoffFunction

namespace PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Remark 4.2. If `>` is well-founded on `ℒ`, there is no infinite strictly increasing sequence,
so the weak ascending chain condition holds. -/
instance {μ : PayoffFunction ℒ S} [WellFoundedGT ℒ] : μ.WeakACC :=
  ⟨fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf)⟩

section LinearOrder

variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- Definition 4.5 (consequence for Proposition 4.1). A slope-like payoff satisfies the weakening
at `⊤`. -/
instance [hμ : μ.IsSlopeLike] : μ.WeakSlopeLikeAtTop :=
  ⟨fun z hz ↦ (hμ.slopelike z.left z.right ⊤ ⟨z.lt, hz⟩).1.imp id le_of_lt⟩

/-- Definition 4.5 (consequence for Proposition 4.3). A slope-like payoff satisfies the weakening
at `⊥`. -/
instance [hμ : μ.IsSlopeLike] : μ.WeakSlopeLikeAtBot :=
  ⟨fun z hz ↦ (hμ.slopelike ⊥ z.left z.right ⟨hz, z.lt⟩).2.2.1.elim (Or.inr ∘ le_of_lt) Or.inl⟩

end LinearOrder

/-! ### Player A's value -/

variable {μ : PayoffFunction ℒ S}

/-- Auxiliary bad set for Proposition 4.1. Endpoints `y < ⊤` for which player A cannot bound all
responses by `μ (y, ⊤)`. -/
private def badSet (μ : PayoffFunction ℒ S) : Set ℒ :=
  {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬ μ ⟨xA, xB, hAB⟩ ≤ μ ⟨YA, ⊤, h⟩}

/-- Auxiliary bad sequence for Proposition 4.1. A strictly increasing sequence of bad endpoints,
constructed from a nonempty set of bad endpoints. -/
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

/-- Auxiliary infimum identity for Proposition 4.1. -/
private lemma iInf_top_eq_min_top (μ : PayoffFunction ℒ S) :
    ⨅ (x : ℒ) (hx : x < ⊤), μ ⟨x, ⊤, hx⟩ = μ.min ⊤ :=
  le_antisymm (le_iInf₂ fun u hu ↦ iInf₂_le u hu.2)
    (le_iInf₂ fun x hx ↦ iInf₂_le x ⟨bot_le, hx⟩)

/-- Proposition 4.1 (equality). Under the weak ascending chain condition and the weak slope-like
condition at `⊤`, the value when A moves first is the infimum of the payoffs on `(x, ⊤)` for
`x < ⊤`. -/
theorem A_top_eq_min_top [h₁ : μ.WeakACC] [h₂ : μ.WeakSlopeLikeAtTop] :
    μ.A ⊤ = μ.min ⊤ := by
  apply le_antisymm
  · -- If no move gives the required bound, the bad moves form a chain violating WeakACC.
    have exists_move : ∀ yA : ℒ, (hyA : yA < ⊤) →
        ∃ xA : ℒ, xA < ⊤ ∧ ∀ xB : ℒ, (hAB : xA < xB) →
          μ ⟨xA, xB, hAB⟩ ≤ μ ⟨yA, ⊤, hyA⟩ := by
      by_contra! hbad
      let Y := badSeq μ hbad
      have hmono : StrictMono (fun n ↦ (Y n : ℒ)) := strictMono_nat_of_lt_succ fun n ↦
        ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose
      obtain ⟨N, hN⟩ := h₁.exists_le (fun n ↦ Y n) hmono
      exact ((Y N).prop.out.choose_spec (Y N) (Y N).prop.out.choose).choose_spec.choose_spec hN
    refine le_min fun yA hyA ↦ ?_
    obtain ⟨xA, hxA, hbound⟩ := exists_move yA hyA.2
    calc
      μ.A ⊤ ≤ μ.max ⟨xA, ⊤, hxA⟩ := A_le (I := ⊤) ⟨bot_le, hxA⟩
      _ ≤ μ ⟨yA, ⊤, hyA.2⟩ := max_le fun xB hxB ↦ hbound xB hxB.1
  · exact le_A fun x hx ↦ (min_le hx).trans apply_le_max

/-- Proposition 4.1 (first-mover advantage). The first-mover advantage under the weak ascending
chain condition and the weak slope-like condition at `⊤`. -/
theorem A_top_le_B_top [μ.WeakACC] [μ.WeakSlopeLikeAtTop] : μ.A ⊤ ≤ μ.B ⊤ :=
  A_top_eq_min_top.trans_le <| le_iSup₂_of_le ⊤ ⟨bot_lt_top, le_rfl⟩ le_rfl

/-! ### Duality and player B's value -/

/-- Auxiliary duality for Proposition 4.3. `StrongDCC` for `μ` gives `WeakACC` for the dual payoff
function. -/
instance [h₁ : μ.StrongDCC] : μ.dual.WeakACC :=
  ⟨fun xd smf ↦ h₁.exists_le (fun n ↦ (xd n).ofDual) fun _ _ hab ↦ smf hab⟩

/-- Auxiliary duality for Proposition 4.3. `WeakSlopeLikeAtBot` for `μ` gives `WeakSlopeLikeAtTop`
for the dual payoff function. -/
instance [h₂ : μ.WeakSlopeLikeAtBot] : μ.dual.WeakSlopeLikeAtTop :=
  ⟨fun z hz ↦ h₂.le_or_le ⟨z.right, z.left, z.lt⟩ hz⟩

/-- Section 4.2 (duality preceding Proposition 4.3). Duality exchanges the game values: player A's
value of `μ.dual` is player B's value of `μ`. -/
theorem A_top_dual : OrderDual.ofDual (μ.dual.A ⊤) = μ.B ⊤ :=
  le_antisymm
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le (OrderDual.ofDual a) ⟨ha.2, ha.1⟩
      (le_iInf₂ fun b hb ↦ iInf₂_le b ⟨hb.2, hb.1⟩))
    (iSup₂_le fun a ha ↦ le_iSup₂_of_le (OrderDual.toDual a) ⟨ha.2, ha.1⟩
      (le_iInf₂ fun b hb ↦ iInf₂_le b ⟨hb.2, hb.1⟩))

/-- Section 4.2 (duality preceding Proposition 4.3). Duality exchanges the game values: player B's
value of `μ.dual` is player A's value of `μ`. -/
theorem B_top_dual : OrderDual.ofDual (μ.dual.B ⊤) = μ.A ⊤ :=
  le_antisymm
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le (OrderDual.toDual a) ⟨ha.2, ha.1⟩
      (iSup₂_le fun b hb ↦ le_iSup₂_of_le b ⟨hb.2, hb.1⟩ le_rfl))
    (le_iInf₂ fun a ha ↦ iInf₂_le_of_le (OrderDual.ofDual a) ⟨ha.2, ha.1⟩
      (iSup₂_le fun b hb ↦ le_iSup₂_of_le b ⟨hb.2, hb.1⟩ le_rfl))

/-- Auxiliary supremum identity for Proposition 4.3. -/
private lemma iSup_bot_eq_max_top (μ : PayoffFunction ℒ S) :
    ⨆ (y : ℒ) (hy : ⊥ < y), μ ⟨⊥, y, hy⟩ = μ.max ⊤ :=
  le_antisymm (iSup₂_le fun y hy ↦ le_iSup₂_of_le y ⟨hy, le_top⟩ le_rfl)
    (iSup₂_le fun y hy ↦ le_iSup₂_of_le y hy.1 le_rfl)

/-- Proposition 4.3 (equality). Under the strong descending chain condition and the weak
slope-like condition at `⊥`, the value when B moves first is the supremum of the payoffs on
`(⊥, x)` for `⊥ < x`. -/
theorem B_top_eq_max_top [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] : μ.B ⊤ = μ.max ⊤ := by
  calc
    μ.B ⊤ = OrderDual.ofDual (μ.dual.A ⊤) := A_top_dual.symm
    _ = OrderDual.ofDual (μ.dual.min ⊤) := congrArg OrderDual.ofDual A_top_eq_min_top
    _ = μ.max ⊤ := by rw [← iInf_top_eq_min_top, ← iSup_bot_eq_max_top]; rfl

/-- Proposition 4.3 (first-mover advantage). The first-mover advantage under the strong descending
chain condition and the weak slope-like condition at `⊥`. -/
theorem A_top_le_B_top_of_strongDCC [μ.StrongDCC] [μ.WeakSlopeLikeAtBot] : μ.A ⊤ ≤ μ.B ⊤ := by
  rw [← A_top_dual, ← B_top_dual]
  exact A_top_le_B_top (μ := μ.dual)

omit [Nontrivial ℒ] in
/-- Remark 4.4. A monotone real-valued rank function with well-ordered range yields the strong
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
/-- Auxiliary interval version of Proposition 4.1 using Remark 4.2. If `>` is well-founded on `ℒ`,
a slope-like payoff function satisfies `μ.min I = μ.A I` on every interval `I`. -/
lemma IsSlopeLike.min_eq_A [WellFoundedGT ℒ] (hsl : μ.IsSlopeLike) (I : StrictIntvl ℒ) :
    μ.min I = μ.A I := by
  simpa only [A_restrict_apply, min_restrict_apply, StrictIntvl.ofSub_top] using
    (A_top_eq_min_top (μ := μ.restrict I)).symm

end SlopeLike

end PayoffFunction

end HarderNarasimhan.Impl
