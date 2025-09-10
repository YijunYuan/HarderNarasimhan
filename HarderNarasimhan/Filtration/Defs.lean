import HarderNarasimhan.Semistability.Results

open Classical

namespace HarderNarasimhan

class μ_Admissible {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) where
  μ_adm : (IsTotal S (· ≤ ·)) ∨ ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I


@[ext]
structure HarderNarasimhanFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] where
  filtration           : ℕ → ℒ
  monotone             : Monotone filtration
  first_eq_bot         : filtration 0 = ⊥
  fin_len              : ∃ n : ℕ, filtration n = ⊤
  strict_mono          : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration i < filtration j
  piecewise_semistable : ∀ i : ℕ, (h: i < Nat.find (fin_len)) → Semistable (Resμ ⟨(filtration i, filtration (i+1)), strict_mono i (i+1) (lt_add_one i) h⟩ μ)
  μA_pseudo_strict_anti: ∀ i : ℕ, (hi : i + 1 < Nat.find fin_len) → ¬ μA μ ⟨(filtration i, filtration (i+1)), strict_mono i (i+1) (lt_add_one i) <| by omega⟩ ≤ μA μ ⟨(filtration (i+1), filtration (i+2)), strict_mono (i+1) (i+2) (by linarith) (by linarith)⟩

end HarderNarasimhan
