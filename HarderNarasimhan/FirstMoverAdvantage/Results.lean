import HarderNarasimhan.FirstMoverAdvantage.Impl


lemma proposition_4_1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) :
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
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩) :
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
∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩
------------
:= impl.rmk4d4 μ r hr₁ hr₂ h
