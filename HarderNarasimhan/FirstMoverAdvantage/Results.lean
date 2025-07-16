import HarderNarasimhan.FirstMoverAdvantage.Defs


lemma proposition_4_1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : prop_4_1_cond₁ μ) (h₂ : prop_4_1_cond₂ μ) :
------------
(
  μAstar ℒ S μ = μmin μ TotIntvl
) ∧ (
  μAstar ℒ S μ ≤ μBstar ℒ S μ
)
------------
:= ⟨impl.prop4d1₁ ℒ S μ h₁ h₂, impl.prop4d1₂ ℒ S μ h₁ h₂⟩


lemma dualμAstar_eq_μBstar {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
(μAstar ℒᵒᵈ Sᵒᵈ fun p ↦ μ ⟨(p.val.2, p.val.1), p.prop⟩).ofDual = μBstar ℒ S μ
------------
:= impl.dualμAstar_eq_μBstar μ


lemma dualμBstar_eq_μAstar {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
OrderDual.ofDual (μBstar ℒᵒᵈ Sᵒᵈ fun p ↦ μ ⟨(p.val.2, p.val.1), p.prop⟩) = μAstar ℒ S μ
------------
:= impl.dualμBstar_eq_μAstar μ


lemma proposition_4_3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : prop_4_3_cond₁ μ) (h₂ : prop_4_3_cond₂ μ) :
------------
(
  μBstar ℒ S μ = μmax μ TotIntvl
) ∧ (
  μAstar ℒ S μ ≤ μBstar ℒ S μ
)
------------
:= ⟨impl.prop4d3₁ μ h₁ h₂, impl.prop4d3₂ μ h₁ h₂⟩


lemma remark_4_4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
(h : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z.val.1 = r z.val.2 → μ z = ⊤) :
------------
prop_4_3_cond₁ μ
------------
:= impl.rmk4d4 μ r hr₁ hr₂ h
