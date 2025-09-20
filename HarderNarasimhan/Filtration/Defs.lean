import HarderNarasimhan.Semistability.Results
import Mathlib.Order.RelSeries
open Classical

namespace HarderNarasimhan

class μ_Admissible {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) where
  μ_adm : (IsTotal S (· ≤ ·)) ∨ ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} :
μ_Admissible μ where
  μ_adm := Or.inl LE.isTotal

@[ext]
structure HarderNarasimhanFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) where
  filtration           : ℕ → ℒ
  monotone             : Monotone filtration
  first_eq_bot         : filtration 0 = ⊥
  fin_len              : ∃ n : ℕ, filtration n = ⊤
  strict_mono          : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration i < filtration j
  piecewise_semistable : ∀ i : ℕ, (h: i < Nat.find (fin_len)) → Semistable (Resμ ⟨(filtration i, filtration (i+1)), strict_mono i (i+1) (lt_add_one i) h⟩ μ)
  μA_pseudo_strict_anti: ∀ i : ℕ, (hi : i + 1 < Nat.find fin_len) → ¬ μA μ ⟨(filtration i, filtration (i+1)), strict_mono i (i+1) (lt_add_one i) <| le_of_lt hi⟩ ≤ μA μ ⟨(filtration (i+1), filtration (i+2)), strict_mono (i+1) (i+2) (Nat.lt_add_one (i + 1)) hi⟩

def IsIntervalSemistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(x y : ℒ) : Prop :=
  ∃ h : x < y, Semistable (Resμ ⟨(x, y), h⟩ μ)

def IntervalSemistableRel {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
: SetRel ℒ ℒ :=
{(x, y) | ∃ h : x < y, Semistable (Resμ ⟨(x, y), h⟩ μ)}
end HarderNarasimhan
