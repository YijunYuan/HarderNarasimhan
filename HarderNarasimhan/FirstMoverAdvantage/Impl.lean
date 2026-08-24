/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Semistability.Results
import HarderNarasimhan.FirstMoverAdvantage.Defs
import Mathlib.Data.Real.Basic

/-!
  # First-mover advantage: internal implementation lemmas

  This file contains the internal proofs used to relate the “A/B-star” quantities
  (`μAstar`, `μBstar`) to the global extremal values on `⊤`.

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

/-- `prop4d1_badSet μ` is the set of “bad” first moves for player A: elements `YA < ⊤`
  such that every `xA < ⊤` admits a follow-up `xB` whose payoff is not bounded by
  `μ ⟨YA, ⊤, _⟩`.

  Proposition 4.1 is proved by showing this set is empty.
-/
def prop4d1_badSet {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) : Set ℒ :=
  {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨xA, xB, hAB⟩ ≤ μ ⟨YA, ⊤, h⟩}

/-- `prop4d1₁_seq` is the auxiliary sequence used in the contradiction argument for
  Proposition 4.1.

  Starting from a nonempty set of “bad” candidates `YA`, it recursively constructs
  a new candidate by applying the witness condition at the previous step.
-/
noncomputable def prop4d1₁_seq {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) [h₂ : WeakSlopeLike₁ μ]
(h₃ : (prop4d1_badSet μ).Nonempty) (k : ℕ) : prop4d1_badSet μ :=
  match k with
  | 0 => ⟨h₃.choose,h₃.choose_spec⟩
  | k + 1 => by
    let prop4d1₁_seqkp1 := (prop4d1₁_seq μ h₃ k).prop.out.choose_spec
      (prop4d1₁_seq μ h₃ k) (prop4d1₁_seq μ h₃ k).prop.out.choose
    have h''' := prop4d1₁_seqkp1.choose_spec.choose_spec
    have h' : prop4d1₁_seqkp1.choose < ⊤ := lt_top_iff_ne_top.2 fun hcon ↦
      h''' (le_of_eq <| congrArg μ <| Intvl.ext rfl hcon)
    have hle := (h₂.wsl₁ ⟨prop4d1₁_seq μ h₃ k, prop4d1₁_seqkp1.choose,
      prop4d1₁_seqkp1.choose_spec.choose⟩ h').resolve_left h'''
    refine ⟨prop4d1₁_seqkp1.choose, h', fun xA hxA ↦ ?_⟩
    obtain ⟨xB, hAB, con⟩ := (prop4d1₁_seq μ h₃ k).prop.out.choose_spec xA hxA
    exact ⟨xB, hAB, fun hcon ↦ con (hcon.trans hle)⟩



/-- `prop4d1_helper` rewrites the “top-anchored” sInf that appears naturally in the
  proof of Proposition 4.1 as `μmin μ ⊤`.
-/
lemma prop4d1_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
sInf {x | ∃ x_1, ∃ (hx : x_1 < ⊤), μ ⟨x_1, ⊤, hx⟩ = x} = μmin μ ⊤ :=
  congrArg sInf <| Set.ext fun _ ↦
    ⟨fun ⟨w, hw, hw'⟩ ↦ ⟨w, ⟨Intvl.mem_top w, ne_top_of_lt hw⟩, hw'⟩,
     fun ⟨w, hw, hw'⟩ ↦ ⟨w, lt_top_iff_ne_top.2 hw.2, hw'⟩⟩



/-- `prop4d1₁` is the core statement behind Proposition 4.1: under the two hypotheses
  `h₁` (a weak “eventual improvement” along strict chains) and `h₂` (a weak slope-like
  alternative towards the top), the best-response value `μAstar μ` coincides with the
  global infimum `μmin μ ⊤`.
-/
lemma prop4d1₁ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : Intvl ℒ → S)
[h₁ : WeakAscendingChainCondition μ] [h₂ : WeakSlopeLike₁ μ] :
μAstar μ = μmin μ ⊤ := by
  rw [← prop4d1_helper]
  have : ∀ yA : ℒ, (hyA : yA < ⊤) → ∃ xA : ℒ, xA < ⊤ ∧ (∀ xB : ℒ, (hAB : xA < xB) →
    μ ⟨xA, xB, hAB⟩ ≤ μ ⟨yA, ⊤, hyA⟩) := by
    by_contra!
    let Y := prop4d1₁_seq μ this
    have hsmf : StrictMono (fun n ↦ Y n) := strictMono_nat_of_lt_succ fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose
    have hfinal : ∀ n : ℕ, ¬ μ ⟨Y n, Y (n+1), hsmf (Nat.lt_add_one n)⟩ ≤
        μ ⟨Y n, ⊤, lt_of_lt_of_le (hsmf (Nat.lt_add_one n)) le_top⟩ := fun n ↦
      ((Y n).prop.out.choose_spec (Y n) (Y n).prop.out.choose).choose_spec.choose_spec
    obtain ⟨N, hN⟩ := h₁.wacc (fun n ↦ Y n) hsmf
    exact hfinal N hN
  refine le_antisymm ?_ ?_
  · refine le_sInf fun y ⟨yA, hyA, h⟩ ↦ ?_
    obtain ⟨xA, hxA, h'⟩ := this yA hyA
    exact h.symm ▸ sInf_le_of_le ⟨xA, ⟨Intvl.mem_top xA, ne_top_of_lt hxA⟩, rfl⟩
      (sSup_le fun _ ⟨xB, hxB, hxB'⟩ ↦ hxB' ▸ h' xB (lt_of_le_of_ne hxB.1.1 hxB.2))
  · refine le_sInf fun t ⟨x, hx, h⟩ ↦ h.symm ▸
      sInf_le_of_le ⟨x, lt_top_iff_ne_top.2 hx.2, rfl⟩
      (le_sSup ⟨⊤, ⟨⟨le_top, le_top⟩, hx.2⟩, rfl⟩)



/-- `prop4d1₂` is the easy inequality direction derived from `prop4d1₁`:
  once `μAstar μ = μmin μ ⊤`, we get `μAstar μ ≤ μBstar μ` by exhibiting a
  single witness in the defining `sSup` for `μBstar`.
-/
lemma prop4d1₂ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : Intvl ℒ → S)
[h₁ : WeakAscendingChainCondition μ] [h₂ : WeakSlopeLike₁ μ] :
μAstar μ ≤ μBstar μ :=
  (prop4d1₁ ℒ S μ).trans_le <| le_sSup ⟨⊤, ⟨⟨bot_le, le_rfl⟩, ne_of_lt bot_lt_top⟩, rfl⟩



/-- `dual_wacc_of_sdcc` transports a strong descending chain condition on `μ` to the
  weak ascending chain condition for the dualised slope on `ℒᵒᵈ`.
-/
lemma dual_wacc_of_sdcc {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : Intvl ℒ → S}
[h₁ : StrongDescendingChainCondition μ] :
WeakAscendingChainCondition (fun (p : Intvl ℒᵒᵈ) ↦
  OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩) :=
  ⟨fun xd smf ↦ h₁.wdcc (fun n ↦ (xd n).ofDual) fun _ _ hab ↦ smf hab⟩



/-- `dual_wsl₁_of_wsl₂` transports the second weak slope-like axiom on `μ` to the
  first weak slope-like axiom for the dualised slope on `ℒᵒᵈ`.
-/
lemma dual_wsl₁_of_wsl₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : Intvl ℒ → S}
[h₂ : WeakSlopeLike₂ μ] :
WeakSlopeLike₁ (fun (p : Intvl ℒᵒᵈ) ↦
  OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩) :=
  ⟨fun z hz ↦ h₂.wsl₂ ⟨z.right, z.left, z.lt⟩ hz⟩



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
    refine ⟨a, ⟨Intvl.mem_top a, Ne.symm ha.2⟩, ha' ▸ congrArg sInf (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨Intvl.mem_top (OrderDual.toDual a), Ne.symm ha.2⟩,
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
    refine ⟨a, ⟨Intvl.mem_top a, Ne.symm ha.2⟩, ha' ▸ congrArg sSup (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩
  · rintro ⟨a, ha, ha'⟩
    refine ⟨a, ⟨Intvl.mem_top (OrderDual.toDual a), Ne.symm ha.2⟩,
      ha'.symm ▸ congrArg sInf (Set.ext fun r ↦ ?_)⟩
    exact ⟨fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩,
      fun ⟨b, hb, hb'⟩ ↦ ⟨b, ⟨⟨hb.1.2, hb.1.1⟩, Ne.symm hb.2⟩, hb'⟩⟩



/-- `prop4d3_helper` rewrites the “bottom-anchored” sSup that appears naturally in the
  dual argument as `μmax μ ⊤`.
-/
lemma prop4d3_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
sSup {μ ⟨⊥, y,hy⟩ | (y : ℒ) (hy : ⊥ < y) } = μmax μ ⊤ :=
  congrArg sSup <| Set.ext fun _ ↦
    ⟨fun ⟨w, hw, hw'⟩ ↦ ⟨w, ⟨Intvl.mem_top w, ne_of_lt hw⟩, hw'⟩,
     fun ⟨w, hw, hw'⟩ ↦ ⟨w, bot_lt_iff_ne_bot.2 (Ne.symm hw.2), hw'⟩⟩



/-- `prop4d3₁` is the dual form of Proposition 4.1: under hypotheses `h₁` and `h₂`
  phrased for strict anti-chains and bottom-anchored alternatives, the best-response
  value `μBstar μ` coincides with the global supremum `μmax μ ⊤`.

  The proof reduces to `prop4d1₁` on the order dual, and then translates the result
  back via the duality lemmas.
-/
lemma prop4d3₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
[h₁ : StrongDescendingChainCondition μ] [h₂ : WeakSlopeLike₂ μ] :
μBstar μ = μmax μ ⊤ := by
  have := dual_wacc_of_sdcc (μ := μ)
  have := dual_wsl₁_of_wsl₂ (μ := μ)
  have := prop4d1₁ ℒᵒᵈ Sᵒᵈ (fun (p : Intvl ℒᵒᵈ) ↦ OrderDual.toDual <|
    μ ⟨p.right, p.left, p.lt⟩)
  rw [← prop4d1_helper] at this
  rw [← prop4d3_helper, ← dualμAstar_eq_μBstar, this]
  rfl



/-- `prop4d3₂` packages the inequality direction corresponding to `prop4d3₁`.
  It is obtained by combining the two duality equalities with `prop4d1₂` on `ℒᵒᵈ`.
-/
lemma prop4d3₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
[h₁ : StrongDescendingChainCondition μ] [h₂ : WeakSlopeLike₂ μ] :
μAstar μ ≤ μBstar μ := by
  have := dual_wacc_of_sdcc (μ := μ)
  have := dual_wsl₁_of_wsl₂ (μ := μ)
  exact (dualμAstar_eq_μBstar μ) ▸ (dualμBstar_eq_μAstar μ) ▸
    prop4d1₂ ℒᵒᵈ Sᵒᵈ (fun (p : Intvl ℒᵒᵈ) ↦ OrderDual.toDual <| μ ⟨p.right, p.left, p.lt⟩)



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
