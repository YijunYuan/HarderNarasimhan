import Mathlib.RingTheory.Spectrum.Prime.Basic
import HarderNarasimhan.Interval
open HarderNarasimhan

lemma quest {R : Type} [CommRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]
(N₁ N₂ : Submodule R M) (hN : N₁ < N₂)
(W : Submodule R M) (hW : N₁ ≤ W ∧ W ≤ N₂)
(q : ↥(Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) W)) ⧸
  Submodule.submoduleOf ⊥ (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) W))) :
Quotient.out q.out.val ∈ W.submoduleOf N₂ := by
  sorry

lemma quest' {R : Type} [CommRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]
(N₁ N₂ : Submodule R M) (hN : N₁ < N₂)
(W : Submodule R M) (hW : N₁ ≤ W ∧ W ≤ N₂)
(q : ↥(Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) W)) ⧸
  Submodule.submoduleOf ⊥ (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) W))) :
Quotient.out q.out.val ∈ W.submoduleOf N₂ := by
  refine Submodule.mem_comap.mpr ?_
  obtain ⟨x, hx₁, hx₂⟩ := Submodule.mem_map.mp q.out.property
  rw [Submodule.mem_comap] at hx₁
  show (Quotient.out q.out.val).val ∈ W
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul (N₁.submoduleOf N₂).toAddSubgroup x
  change Quotient.out ((N₁.submoduleOf N₂).mkQ x) = x + y.val at hy
  rw [← hx₂, hy]
  show x.val + y.val.val ∈ W
  refine Submodule.add_mem _ ?_ ?_
  · exact hx₁
  · exact hW.left y.property
