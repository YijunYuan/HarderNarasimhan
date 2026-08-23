/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Semistability.Results
import Mathlib.Data.Real.Basic

/-!
  # First-mover advantage: internal implementation lemmas

  This file contains the internal proofs used to relate the “A/B-star” quantities
  (`μAstar`, `μBstar`) to the global extremal values on `TotIntvl`.

  The main results are Proposition 4.1 (the characterisation of `μAstar`) and
  Proposition 4.3 (the dual characterisation of `μBstar`), together with the
  order-duality lemmas transporting hypotheses and rewriting `μAstar`/`μBstar`.

  All declarations here live in the private `HarderNarasimhan.impl` namespace and
  are intended to be used by the public-facing `Results` files.

  API note: downstream users should normally import
  `HarderNarasimhan.FirstMoverAdvantage.Results` instead of this implementation file.
-/

namespace HarderNarasimhan

namespace impl

/-- `prop4d1₁_seq` is the auxiliary sequence used in the contradiction argument for
  Proposition 4.1.

  Starting from a nonempty set of “bad” candidates `YA`, it recursively constructs
  a new candidate by applying the witness condition at the previous step.
-/
noncomputable def prop4d1₁_seq {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
  ∃ N : ℕ, μ ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩ ≤
    μ ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : Intvl ℒ, (hz :z.right < ⊤) →
  μ z ≤ μ ⟨z.left, ⊤,lt_trans z.lt hz⟩ ∨ μ ⟨z.right, ⊤,hz⟩ ≤
  μ ⟨z.left, ⊤,lt_trans z.lt hz⟩)
(h₃ : {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB),
  ¬μ ⟨xA, xB, hAB⟩ ≤ μ ⟨YA, ⊤, h⟩}.Nonempty) (k : ℕ)
: {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨xA, xB, hAB⟩ ≤ μ ⟨YA, ⊤, h⟩} :=
  match k with
  | 0 => ⟨h₃.choose,h₃.choose_spec⟩
  | k + 1 => by
    let prop4d1₁_seqkp1 := (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose_spec
      (prop4d1₁_seq μ h₁ h₂ h₃ k) (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose
    have h''' := prop4d1₁_seqkp1.choose_spec.choose_spec
    have h' : prop4d1₁_seqkp1.choose < ⊤ := lt_top_iff_ne_top.2 fun hcon ↦
      h''' (le_of_eq <| congrArg μ <| Intvl.ext rfl hcon)
    have hle := (h₂ ⟨prop4d1₁_seq μ h₁ h₂ h₃ k, prop4d1₁_seqkp1.choose,
      prop4d1₁_seqkp1.choose_spec.choose⟩ h').resolve_left h'''
    refine ⟨prop4d1₁_seqkp1.choose, h', fun xA hxA ↦ ?_⟩
    obtain ⟨xB, hAB, con⟩ := (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose_spec xA hxA
    exact ⟨xB, hAB, fun hcon ↦ con (hcon.trans hle)⟩



/-- `prop4d1_helper` rewrites the “top-anchored” sInf that appears naturally in the
  proof of Proposition 4.1 as `μmin μ TotIntvl`.
-/
lemma prop4d1_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
sInf {x | ∃ x_1, ∃ (hx : x_1 < ⊤), μ ⟨x_1, ⊤, hx⟩ = x} = μmin μ TotIntvl :=
  congrArg sInf <| Set.ext fun _ ↦
    ⟨fun ⟨w, hw, hw'⟩ ↦ ⟨w, ⟨in_TotIntvl w, ne_top_of_lt hw⟩, hw'⟩,
     fun ⟨w, hw, hw'⟩ ↦ ⟨w, lt_top_iff_ne_top.2 hw.2, hw'⟩⟩



/-- `prop4d1₁` is the core statement behind Proposition 4.1: under the two hypotheses
  `h₁` (a weak “eventual improvement” along strict chains) and `h₂` (a weak slope-like
  alternative towards the top), the best-response value `μAstar μ` coincides with the
  global infimum `μmin μ TotIntvl`.
-/
lemma prop4d1₁ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
  ∃ N : ℕ, μ ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩ ≤
    μ ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : Intvl ℒ, (hz :z.right < ⊤) →
  μ z ≤ μ ⟨z.left, ⊤,lt_trans z.lt hz⟩ ∨ μ ⟨z.right, ⊤,hz⟩ ≤
  μ ⟨z.left, ⊤,lt_trans z.lt hz⟩) :
μAstar μ = μmin μ TotIntvl := by
  rw [← prop4d1_helper]
  have : ∀ yA : ℒ, (hyA : yA < ⊤) → ∃ xA : ℒ, xA < ⊤ ∧ (∀ xB : ℒ, (hAB : xA < xB) →
    μ ⟨xA, xB, hAB⟩ ≤ μ ⟨yA, ⊤, hyA⟩) := by
    by_contra!
    let Y := prop4d1₁_seq μ h₁ h₂ this
    have hsmf : StrictMono (fun n ↦ Y n) := strictMono_nat_of_lt_succ fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose
    have hfinal : ∀ n : ℕ, ¬ μ ⟨Y n, Y (n+1), hsmf (Nat.lt_add_one n)⟩ ≤
        μ ⟨Y n, ⊤, lt_of_lt_of_le (hsmf (Nat.lt_add_one n)) le_top⟩ := fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose_spec
    obtain ⟨N, hN⟩ := h₁ (fun n ↦ Y n) hsmf
    exact hfinal N hN
  refine le_antisymm ?_ ?_
  · refine le_sInf fun y ⟨yA, hyA, h⟩ ↦ ?_
    obtain ⟨xA, hxA, h'⟩ := this yA hyA
    exact h.symm ▸ sInf_le_of_le ⟨xA, ⟨in_TotIntvl xA, ne_top_of_lt hxA⟩, rfl⟩
      (sSup_le fun _ ⟨xB, hxB, hxB'⟩ ↦ hxB' ▸ h' xB (lt_of_le_of_ne hxB.1.1 hxB.2))
  · refine le_sInf fun t ⟨x, hx, h⟩ ↦ h.symm ▸
      sInf_le_of_le ⟨x, lt_top_iff_ne_top.2 hx.2, rfl⟩
      (le_sSup ⟨⊤, ⟨⟨le_top, le_top⟩, hx.2⟩, rfl⟩)



/-- `prop4d1₂` is the easy inequality direction derived from `prop4d1₁`:
  once `μAstar μ = μmin μ TotIntvl`, we get `μAstar μ ≤ μBstar μ` by exhibiting a
  single witness in the defining `sSup` for `μBstar`.
-/
lemma prop4d1₂ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) →
  ∃ N : ℕ, μ ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩ ≤
    μ ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : Intvl ℒ, (hz :z.right < ⊤) → μ z ≤
  μ ⟨z.left, ⊤,lt_trans z.lt hz⟩ ∨ μ ⟨z.right, ⊤,hz⟩ ≤ μ ⟨z.left, ⊤,lt_trans z.lt hz⟩) :
μAstar μ ≤ μBstar μ :=
  (prop4d1₁ ℒ S μ h₁ h₂).trans_le <| le_sSup ⟨⊤, ⟨⟨bot_le, le_rfl⟩, ne_of_lt bot_lt_top⟩, rfl⟩



/-- Coercion sending an interval in `ℒ` to the corresponding interval in the order dual.
  This swaps the endpoints.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
Coe (Intvl ℒ) (Intvl ℒᵒᵈ) where
  coe p := ⟨p.right, p.left, p.lt⟩


/-- Coercion sending an interval in `ℒᵒᵈ` back to an interval in `ℒ`.
  This is the same endpoint swap, viewed in the opposite direction.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] :
Coe (Intvl ℒᵒᵈ) (Intvl ℒ) where
  coe p := ⟨p.right, p.left, p.lt⟩


/-- Coercion transporting a function `μ` on intervals of `ℒ` to a function on intervals
  of `ℒᵒᵈ`, with values in the order dual `Sᵒᵈ`.

  This is a notational convenience for duality arguments.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] :
Coe (Intvl ℒ → S) (Intvl ℒᵒᵈ → Sᵒᵈ) where
  coe f := fun p ↦ f p


/-- `h₁_dual_of_h₁` transports the “descending-chain” hypothesis `h₁` on `ℒ` to the
  corresponding “ascending-chain” hypothesis on the order dual `ℒᵒᵈ`.
-/
lemma h₁_dual_of_h₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : Intvl ℒ → S}
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) →
  ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤
    μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩) :
(∀ x : ℕ → ℒᵒᵈ, (smf : StrictMono x) →
  ∃ N : ℕ, @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ)
  ⟨x N, x (N+1), smf <| Nat.lt_add_one N⟩)  ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ)
  ⟨x N, ⊤, lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)) :=
  fun xd smf ↦ h₁ (fun n ↦ (xd n).ofDual) fun _ _ hab ↦ smf hab



/-- `h₂_dual_of_h₂` transports the “bottom-anchored” weak alternative `h₂` to the
  corresponding “top-anchored” alternative on `ℒᵒᵈ`.
-/
lemma h₂_dual_of_h₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : Intvl ℒ → S}
(h₂ : ∀ z : Intvl ℒ, (hz : ⊥ < z.left) →
  μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤ μ z ∨ μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤
  μ ⟨⊥, z.left,hz⟩) :
∀ z : Intvl ℒᵒᵈ, (hz :z.right < ⊤) →
  @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ) z)
    ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ) ⟨z.left, ⊤,lt_trans z.lt hz⟩) ∨
  @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ)
    ⟨z.right, ⊤,hz⟩) ((↑μ : Intvl ℒᵒᵈ → Sᵒᵈ)
    ⟨z.left, ⊤,lt_trans z.lt hz⟩) := fun z hz ↦ h₂ z hz



/-- `dualμAstar_eq_μBstar` identifies `μAstar` computed for the dualised `μ` with
  `μBstar μ`.

  This is an explicit unfolding of definitions and a reindexing of the `sInf`/`sSup`
  expressions.
-/
lemma dualμAstar_eq_μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
OrderDual.ofDual <| μAstar (fun (p : Intvl ℒᵒᵈ) ↦
  OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩) = μBstar μ
:= by
  simp only [μAstar, μA, sInf, ne_eq, OrderDual.exists, μBstar, μB]
  refine congrArg (@sSup S _) <| Set.ext fun x ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨in_TotIntvl a, Ne.symm ha.2⟩, ha' ▸ congrArg sInf (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨in_TotIntvl (OrderDual.toDual a), Ne.symm ha.2⟩,
      ha' ▸ congrArg sSup (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩



/-- `dualμBstar_eq_μAstar` is the dual companion to `dualμAstar_eq_μBstar`.
-/
lemma dualμBstar_eq_μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
OrderDual.ofDual <| μBstar (fun (p : Intvl ℒᵒᵈ) ↦
  OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩) = μAstar μ
:= by
  simp only [μBstar, μB, sSup, ne_eq, OrderDual.exists, μAstar, μA]
  refine congrArg (@sInf S _) <| Set.ext fun x ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨in_TotIntvl a, Ne.symm ha.2⟩, ha' ▸ congrArg sSup (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨in_TotIntvl (OrderDual.toDual a), Ne.symm ha.2⟩,
      ha'.symm ▸ congrArg sInf (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩



/-- `prop4d3_helper` rewrites the “bottom-anchored” sSup that appears naturally in the
  dual argument as `μmax μ TotIntvl`.
-/
lemma prop4d3_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
sSup {μ ⟨⊥, y,hy⟩ | (y : ℒ) (hy : ⊥ < y) } = μmax μ TotIntvl :=
  congrArg sSup <| Set.ext fun _ ↦
    ⟨fun ⟨w, hw, hw'⟩ ↦ ⟨w, ⟨in_TotIntvl w, ne_of_lt hw⟩, hw'⟩,
     fun ⟨w, hw, hw'⟩ ↦ ⟨w, bot_lt_iff_ne_bot.2 (Ne.symm hw.2), hw'⟩⟩



/-- `prop4d3₁` is the dual form of Proposition 4.1: under hypotheses `h₁` and `h₂`
  phrased for strict anti-chains and bottom-anchored alternatives, the best-response
  value `μBstar μ` coincides with the global supremum `μmax μ TotIntvl`.

  The proof reduces to `prop4d1₁` on the order dual, and then translates the result
  back via the duality lemmas.
-/
lemma prop4d3₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) →
  ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤
    μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : Intvl ℒ, (hz : ⊥ < z.left) →
  μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤ μ z ∨ μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤
  μ ⟨⊥, z.left,hz⟩) :
μBstar μ = μmax μ TotIntvl := by
  have := prop4d1₁ ℒᵒᵈ Sᵒᵈ (fun (p : Intvl ℒᵒᵈ) ↦ OrderDual.toDual <|
    μ ⟨p.right, p.left, p.lt⟩) (h₁_dual_of_h₁ h₁) (h₂_dual_of_h₂ h₂)
  rw [← prop4d1_helper] at this
  rw [← prop4d3_helper, ← dualμAstar_eq_μBstar, this]
  rfl



/-- `prop4d3₂` packages the inequality direction corresponding to `prop4d3₁`.
  It is obtained by combining the two duality equalities with `prop4d1₂` on `ℒᵒᵈ`.
-/
lemma prop4d3₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <|
  Nat.lt_add_one N⟩ ≤ μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : Intvl ℒ, (hz : ⊥ < z.left) → μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤ μ z ∨
  μ ⟨⊥, z.right,lt_trans hz z.lt⟩ ≤ μ ⟨⊥, z.left,hz⟩) :
μAstar μ ≤ μBstar μ := (dualμAstar_eq_μBstar μ) ▸ (dualμBstar_eq_μAstar μ) ▸
  prop4d1₂ ℒᵒᵈ Sᵒᵈ (↑μ : Intvl ℒᵒᵈ → Sᵒᵈ) (h₁_dual_of_h₁ h₁) (h₂_dual_of_h₂ h₂)



/-- `rmk4d4` is a well-ordering / ranking-function criterion that produces the
  strict-anti-chain hypothesis needed in `prop4d3₁`.

  Given a monotone rank function `r : ℒ → ℝ` whose range is well-ordered, any strict
  descending chain must eventually stabilise in rank; the hypothesis `h` then forces
  the required inequality by turning equal ranks into a `μ = ⊤` statement.
-/
lemma rmk4d4 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
(h : ∀ z : Intvl ℒ, r z.left = r z.right → μ z = ⊤) :
∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨⊥, x N, lt_of_le_of_lt bot_le <| saf <|
  Nat.lt_add_one N⟩ ≤ μ ⟨x (N+1), x N, saf <| Nat.lt_add_one N⟩ := by
  intro x saf
  obtain ⟨m, hmW, hmin⟩ := hr₂.wf.has_min {s : Set.range r | ∃ N : ℕ, s = r (x N)}
    ⟨⟨r (x 0), Set.mem_range_self (x 0)⟩, 0, rfl⟩
  obtain ⟨n, hn⟩ := hmW
  have heq : r (x n) = r (x (n + 1)) :=
    eq_of_le_of_not_lt' (hr₁ (saf (Nat.lt_add_one n)).le)
      (hn ▸ hmin ⟨r (x (n + 1)), Set.mem_range_self (x (n + 1))⟩ ⟨n + 1, rfl⟩)
  exact ⟨n, (h ⟨x (n + 1), x n, saf (Nat.lt_add_one n)⟩ heq.symm) ▸ le_top⟩

end impl

end HarderNarasimhan
