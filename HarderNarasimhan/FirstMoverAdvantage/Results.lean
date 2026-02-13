import HarderNarasimhan.FirstMoverAdvantage.Defs

/-!
# First-mover advantage: public statements

This file exposes the main lemmas about the values `μAstar` and `μBstar`, together with the
order-theoretic hypotheses used in the first-mover advantage arguments.

The core proofs live in `HarderNarasimhan.FirstMoverAdvantage.Impl`.

API overview:

* This file is the recommended import for working with `μAstar`/`μBstar` and the first-mover
  advantage propositions.
* The internal lemmas are in `HarderNarasimhan.FirstMoverAdvantage.Impl` under
  `HarderNarasimhan.impl`.
-/

namespace HarderNarasimhan

/-
Proposition 4.1: compute player A's value.
Under weak ascending chain condition and a weak slope-like axiom, player A's value `μAstar`
coincides with `μmin` on the total interval, and `μAstar ≤ μBstar`.

API note: this is the main user-facing rewrite for `μAstar` under the standard hypotheses.
-/
lemma proposition_4_1 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : WeakAscendingChainCondition μ) (h₂ : WeakSlopeLike₁ μ) :
(
  μAstar μ = μmin μ TotIntvl
) ∧ (
  μAstar μ ≤ μBstar μ
)
:= ⟨impl.prop4d1₁ ℒ S μ h₁.wacc h₂.wsl₁, impl.prop4d1₂ ℒ S μ h₁.wacc h₂.wsl₁⟩


/--
Duality for `μAstar`.

This expresses the value `μAstar` of the dual slope (on `ℒᵒᵈ`) in terms of `μBstar` of the
original slope.
-/
lemma dualμAstar_eq_μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
OrderDual.ofDual <| μAstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦
  OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μBstar μ
:= impl.dualμAstar_eq_μBstar μ


/--
Duality for `μBstar`.

This expresses the value `μBstar` of the dual slope (on `ℒᵒᵈ`) in terms of `μAstar` of the
original slope.
-/
lemma dualμBstar_eq_μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
OrderDual.ofDual <| μBstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦
  OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μAstar μ
:= impl.dualμBstar_eq_μAstar μ


/-
Proposition 4.3: compute player B's value.
Under strong descending chain condition and the second weak slope-like axiom, player B's value
`μBstar` coincides with `μmax` on the total interval, and `μAstar ≤ μBstar`.

API note: this is the main user-facing rewrite for `μBstar` under the standard hypotheses.
-/
lemma proposition_4_3 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : StrongDescendingChainCondition μ) (h₂ : WeakSlopeLike₂ μ) :
(
  μBstar μ = μmax μ TotIntvl
) ∧ (
  μAstar μ ≤ μBstar μ
)
:= ⟨impl.prop4d3₁ μ h₁.wdcc h₂.wsl₂, impl.prop4d3₂ μ h₁.wdcc h₂.wsl₂⟩


/--
Remark 4.4: a sufficient condition for `StrongDescendingChainCondition`.

Given a real-valued rank function `r : ℒ → ℝ` whose range is well-ordered and such that `μ` is
`⊤` whenever `r` does not strictly decrease along an interval, one obtains the strong descending
chain condition.
-/
lemma remark_4_4 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
(h : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z.val.1 = r z.val.2 → μ z = ⊤) :
StrongDescendingChainCondition μ
:= {wdcc := impl.rmk4d4 μ r hr₁ hr₂ h}

end HarderNarasimhan
