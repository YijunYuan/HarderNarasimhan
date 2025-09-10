import HarderNarasimhan.FirstMoverAdvantage.Defs

namespace HarderNarasimhan

lemma proposition_4_1 {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : WeakAscendingChainCondition μ) (h₂ : WeakSlopeLike₁ μ) :
------------
(
  μAstar μ = μmin μ TotIntvl
) ∧ (
  μAstar μ ≤ μBstar μ
)
------------
:= ⟨impl.prop4d1₁ ℒ S μ h₁.wacc h₂.wsl₁, impl.prop4d1₂ ℒ S μ h₁.wacc h₂.wsl₁⟩


lemma dualμAstar_eq_μBstar {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
OrderDual.ofDual <| μAstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦ OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μBstar μ
------------
:= impl.dualμAstar_eq_μBstar μ


lemma dualμBstar_eq_μAstar {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
OrderDual.ofDual <| μBstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦ OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μAstar μ
------------
:= impl.dualμBstar_eq_μAstar μ


lemma proposition_4_3 {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : WeakDescendingChainCondition μ) (h₂ : WeakSlopeLike₂ μ) :
------------
(
  μBstar μ = μmax μ TotIntvl
) ∧ (
  μAstar μ ≤ μBstar μ
)
------------
:= ⟨impl.prop4d3₁ μ h₁.wdcc h₂.wsl₂, impl.prop4d3₂ μ h₁.wdcc h₂.wsl₂⟩


lemma remark_4_4 {ℒ : Type} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
(h : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z.val.1 = r z.val.2 → μ z = ⊤) :
------------
WeakDescendingChainCondition μ
------------
:= {wdcc := impl.rmk4d4 μ r hr₁ hr₂ h}

end HarderNarasimhan
