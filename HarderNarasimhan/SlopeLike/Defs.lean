import HarderNarasimhan.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.NNReal.Basic
import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion
import HarderNarasimhan.Interval

namespace HarderNarasimhan

class SlopeLike {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  slopelike : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
(
  μ ⟨(x, y), h.1⟩ ≤ μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨ μ ⟨(y, z), h.2⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨ μ ⟨(y, z), h.2⟩ ≤ μ ⟨(x, z), lt_trans h.1 h.2⟩
) ∧ (
  μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩ ∨ μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(y, z), h.2⟩
) ∧ (
  μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μ ⟨(x, y), h.1⟩ ∨ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩
)


class TotallyOrderedRealVectorSpace (V : Type*) extends AddCommGroup V, Module ℝ V, LinearOrder V, PosSMulStrictMono ℝ V where
  elim_AddLeftMono : ∀ {y z : V} (x : V), y ≤ z → x + y ≤ x + z


instance {V : Type*} [TotallyOrderedRealVectorSpace V] : AddLeftMono V where
  elim := fun x _ _ h ↦ TotallyOrderedRealVectorSpace.elim_AddLeftMono x h


noncomputable def μQuotient {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [TotallyOrderedRealVectorSpace V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V): {p :ℒ × ℒ // p.1 < p.2} → OrderTheory.DedekindMacNeilleCompletion V :=
  fun z ↦ if _ : r z > 0 then ↑((r z)⁻¹ • d z) else ⊤


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [hsl : SlopeLike μ]
{z : {p : ℒ × ℒ // p.1 < p.2}} : SlopeLike (Resμ z μ)
:= { slopelike := fun x y z h ↦ hsl.slopelike x.val y.val z.val ⟨lt_iff_le_not_ge.2 h.1,lt_iff_le_not_ge.2 h.2⟩ }

end HarderNarasimhan
