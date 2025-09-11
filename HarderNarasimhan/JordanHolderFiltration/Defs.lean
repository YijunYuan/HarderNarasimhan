import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Order.OrderIsoNat
open Classical

namespace HarderNarasimhan

class FiniteTotalPayoff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  fin_tot_payoff : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤


class WeakDescendingChainCondition' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wdcc' : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤


@[ext]
structure JordanHolderFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
--[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ] [WeakDescendingChainCondition' μ]
where
  filtration : ℕ → ℒ
  antitone : Antitone filtration
  fin_len : ∃ N : ℕ, filtration N =⊥
  strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i
  first_eq_top : filtration 0 = ⊤
  step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨(filtration (k + 1),filtration k),strict_anti k (k+1) (lt_add_one k) hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  step_cond₂ : ∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : WeakDescendingChainCondition' μ] :
WeakDescendingChainCondition μ where
  wdcc := by
    intro f saf
    rcases h.wdcc' f saf with ⟨N, hN⟩
    use N
    exact hN ▸ le_top


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : WeakDescendingChainCondition' μ] {I : {p : ℒ × ℒ // p.1 < p.2}} : WeakDescendingChainCondition' (Resμ I μ) where
  wdcc' := fun f saf ↦ h.wdcc' (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ lt_iff_le_not_le.mpr (saf hn)


class Affine {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  affine : ∀ a b : ℒ, (h : ¬ a ≤ b) → μ ⟨(a ⊓ b, a), inf_lt_left.2 h⟩ = μ ⟨(b, a ⊔ b), right_lt_sup.2 h⟩


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] {I : {p : ℒ × ℒ // p.1 < p.2}} : Affine (Resμ I μ) where
  affine := fun a b h ↦ haff.affine a b h

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] : Convex μ := by
  rw [← impl.Convex_iff]
  refine { convex := ?_ }
  intro x y hx hy hxy
  rw [haff.affine x y hxy]

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ] [hwdcc' : WeakDescendingChainCondition' μ] {x : ℒ} {hx : ⊥ < x}: FiniteTotalPayoff (Resμ ⟨(⊥, x), hx⟩ μ) := by
  refine { fin_tot_payoff := ?_ }
  simp only [Resμ]
  by_contra h
  have : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
    exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
  have := this hst
  simp only [μmax, TotIntvl, ne_eq] at this
  have this_q: μ ⟨(⊥, x), hx⟩ ≤ μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    rw [← this]
    apply le_sSup
    use x, ⟨in_TotIntvl x, Ne.symm <| bot_lt_iff_ne_bot.1 hx⟩
  exact (not_le_of_lt <| h ▸ lt_top_iff_ne_top.2 hftp.fin_tot_payoff) this_q

end HarderNarasimhan
