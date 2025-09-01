import Mathlib.RingTheory.Spectrum.Prime.Basic
import HarderNarasimhan.Interval
open HarderNarasimhan
lemma quest {R : Type} [CommRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]
(N₁ N₂ : Submodule R M) (hN : N₁ < N₂)
(W : Interval ⟨(N₁, N₂), hN⟩) (hW : W ≠ ⊥)
(q : ↥(Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W)) ⧸
  Submodule.submoduleOf ⊥ (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W))) :
Quotient.out q.out.val ∈ Submodule.submoduleOf (↑W) N₂ := by
  have : q.out.val ∈ Submodule.map (N₁.submoduleOf N₂).mkQ (W.val.submoduleOf N₂) := Submodule.coe_mem q.out


  sorry
