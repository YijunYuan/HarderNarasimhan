import HarderNarasimhan.FirstMoverAdvantage.Impl
import HarderNarasimhan.SlopeLike.Defs
import Mathlib.Order.OrderIsoNat
namespace HarderNarasimhan

class WeakAscendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wacc : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩

instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} : WeakAscendingChainCondition μ :=
{wacc := (fun f smf ↦ False.elim (not_strictMono_of_wellFoundedGT f smf))}


class StrongDescendingChainCondition {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wdcc : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩


class WeakSlopeLike₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wsl₁ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩


class WeakSlopeLike₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wsl₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : SlopeLike μ]:
WeakSlopeLike₁ μ := by
  refine { wsl₁ := fun z hz ↦ ?_ }
  cases' (hμ.slopelike z.val.1 z.val.2 ⊤ ⟨z.prop,hz⟩).1 with this this
  · exact Or.inl this
  · exact Or.inr <| le_of_lt this


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : SlopeLike μ]:
WeakSlopeLike₂ μ := by
  refine { wsl₂ := fun z hz ↦ ?_ }
  cases' (hμ.slopelike ⊥ z.val.1 z.val.2 ⟨hz,z.prop⟩).2.2.1 with this this
  · exact Or.inr <| le_of_lt this
  · exact Or.inl this


end HarderNarasimhan
