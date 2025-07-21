import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl
import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
open Classical


class FiniteTotalPayoff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) where
  fin_tot_payoff : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤


class WeakDescendingChainCondition' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) where
  wdcc' : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| by linarith⟩ = ⊤


@[ext]
class JordanHolderFiltration {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ] [WeakDescendingChainCondition' μ] where
  filtration : ℕ → ℒ
  antitone : Antitone filtration
  fin_len : ∃ N : ℕ, filtration N =⊥
  strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i
  first_eq_top : filtration 0 = ⊤
  step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨(filtration (k + 1),filtration k),strict_anti k (k+1) (by linarith) (by linarith)⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  step_cond₂ : ∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (by omega) hi⟩


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : WeakDescendingChainCondition' μ] :
WeakDescendingChainCondition μ where
  wdcc := by
    intro f saf
    rcases h.wdcc' f saf with ⟨N, hN⟩
    use N
    exact hN ▸ le_top
