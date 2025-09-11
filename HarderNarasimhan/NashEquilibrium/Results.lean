import HarderNarasimhan.NashEquilibrium.Impl

namespace HarderNarasimhan

lemma μmin_lt_μ_lt_μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) :
------------
∀ I : {p : ℒ × ℒ // p.1 < p.2}, μmin μ I ≤ μ I ∧ μ I ≤ μmax μ I
------------
:= impl.rmk4d10₀ μ


lemma remark_4_10 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
(
  μBstar μ ≤ μAstar μ ↔ ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) → μmin μ ⟨(⊥,y),hy⟩ ≤ μmax μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx⟩
) ∧
(
  WeakAscendingChainCondition μ → WeakSlopeLike₁ μ →
  (
    NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊥) → μmin μ ⟨(⊥,y),bot_lt_iff_ne_bot.2 hy⟩ ≤ μmin μ TotIntvl
  )
) ∧ (
  StrongDescendingChainCondition μ → WeakSlopeLike₂ μ →
  (
    NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊤) → μmax μ TotIntvl ≤ μmax μ ⟨(y,⊤),lt_top_iff_ne_top.2 hy⟩
  )
)
------------
:= ⟨impl.rmk4d10₁ μ,⟨impl.rmk4d10₂ μ,impl.rmk4d10₃ μ⟩⟩


lemma proposition_4_11 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
(
  μmin μ TotIntvl = μmax μ TotIntvl → μBstar μ ≤ μAstar μ
) ∧ (
  WeakAscendingChainCondition μ → WeakSlopeLike₁ μ →
  StrongDescendingChainCondition μ → WeakSlopeLike₂ μ →
  μBstar μ ≤ μAstar μ → μmin μ TotIntvl = μmax μ TotIntvl
)
------------
:= ⟨impl.prop4d11₁ μ,impl.prop4d11₂ μ⟩


lemma proposition_4_12 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
------------
μmax μ TotIntvl = μ TotIntvl → μmin μ TotIntvl = μmax μ TotIntvl
------------
:= impl.prop4d12 μ h


lemma remark_4_13 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ):
------------
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
  ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩
------------
:= impl.rmk4d13 μ hμ


lemma proposition_4_14 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
------------
μmin μ TotIntvl = μ TotIntvl → μmax μ TotIntvl = μmin μ TotIntvl
------------
:= impl.prop4d14 μ h


lemma remark_4_15 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ) :
------------
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
  μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨
  ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩
------------
:= impl.rmk4d15 μ hμ


lemma proposition_4_16 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ):
------------
(
  List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl
  ]
) ∧ (
  WeakAscendingChainCondition μ → StrongDescendingChainCondition μ →
  List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl,
  NashEquilibrium μ
  ]
)
------------
:= by
  refine ⟨impl.prop4d16₁ μ hμ,fun h₁ h₂ ↦ ?_⟩
  tfae_have 1 ↔ 2 := ((impl.prop4d16₁ μ hμ).out 0 1 (by norm_num) (by norm_num))
  tfae_have 2 ↔ 3 := ((impl.prop4d16₁ μ hμ).out 1 2 (by norm_num) (by norm_num))
  tfae_have 3 ↔ 4 := impl.prop4d16₂ μ hμ h₁ h₂
  tfae_finish


lemma proposition_4_18 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : Semistable μ) :
------------
(
  μBstar μ ≤ μAstar μ
) ∧ (
  (WeakAscendingChainCondition μ ∧ WeakSlopeLike₁ μ) ∨ (StrongDescendingChainCondition μ ∧ WeakSlopeLike₂ μ) →
    NashEquilibrium μ
)
------------
:= ⟨impl.prop4d18₁ μ hμ,impl.prop4d18₂ μ hμ⟩


lemma proposition_4_20 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) →
  WeakAscendingChainCondition (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ))
(h₂ :  ∀ x : ℒ, (hx : x ≠ ⊥) →
  WeakSlopeLike₁ (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ)) :
------------
NashEquilibrium μ → Semistable μ
------------
:= impl.prop4d20 μ h₁ h₂


theorem theorem_4_21 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ)
(h₁ : WeakAscendingChainCondition μ) (h₂ : StrongDescendingChainCondition μ) :
------------
List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl,
  NashEquilibrium μ--,
  --Semistable μ
  ]
∧ (
  Semistable μ → NashEquilibrium μ
) ∧ (
  (∀ x : ℒ, (hx : x ≠ ⊥) → WeakAscendingChainCondition (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ)) →
  NashEquilibrium μ → Semistable μ
)
------------
:= impl.thm4d21 μ hμ h₁ h₂

end HarderNarasimhan
