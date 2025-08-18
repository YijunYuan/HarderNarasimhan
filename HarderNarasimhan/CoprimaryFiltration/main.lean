import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results

namespace HardarNarasimhan

abbrev S₀ (R : Type) [CommRing R] [IsNoetherianRing R] := Finset (LinearExtension (PrimeSpectrum R))

lemma po (R : Type) [CommRing R] [IsNoetherianRing R] : ∃ lo: LinearOrder (S₀ R),  (∀ x y : (S₀ R), x ≤ y → lo.le x y) ∧ ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ lo.le ({p} : (S₀ R)) {q} := by
  sorry

noncomputable instance (priority:=114514) {R : Type} [CommRing R] [IsNoetherianRing R]: LinearOrder (S₀ R) := (po R).choose
noncomputable instance (priority:=114513) {R : Type} [CommRing R] [IsNoetherianRing R]: PartialOrder (S₀ R) := instLinearOrderS₀.toPartialOrder
noncomputable instance (priority:=114512) {R : Type} [CommRing R] [IsNoetherianRing R]: LE (S₀ R) where
  le := instLinearOrderS₀.le

lemma S₀_order {R : Type} [CommRing R] [IsNoetherianRing R]: ∀ p q : LinearExtension (PrimeSpectrum R), p ≤ q ↔ ({p} : (S₀ R)) ≤ ({q} : (S₀ R)) := (po R).choose_spec.2

abbrev S (R : Type) [CommRing R] [IsNoetherianRing R] := @DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

abbrev ℒ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:= Submodule R M

noncomputable abbrev μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R) := fun I ↦ coe'.toFun <| @Set.toFinset (LinearExtension (PrimeSpectrum R)) ({ {asIdeal := p, isPrime := h.out.1} | (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) }) <| (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

lemma strip_μ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, ∃ J : (S₀ R), ↑J = (μ R M) I := by
  intro _
  apply exists_apply_eq_apply

lemma μ_nonempty {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]  [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (strip_μ I).choose.Nonempty := by
  intro I
  rw [coe'.inj.1 (strip_μ I).choose_spec]
  simp only [Set.toFinset_nonempty]
  have := Submodule.Quotient.nontrivial_of_lt_top (Submodule.submoduleOf I.val.1 I.val.2) <| Classical.byContradiction fun this ↦ (ne_of_lt <| lt_of_lt_of_le I.prop <| Submodule.comap_subtype_eq_top.mp <| not_lt_top_iff.1 this) rfl
  rcases associatedPrimes.nonempty R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_setOf.mpr ?_⟩
  use q, hq

lemma noname {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := sorry

instance prop_3_11 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := sorry

lemma prop_3_12 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I = ({((strip_μ I).choose.min' <| μ_nonempty I)} : S₀ R) := by
  intro I

  sorry

instance prop_3_13 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μA_DescendingChainCondition (μ R M) where
  μ_dcc := by
    sorry

lemma rmk4d14₁ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨(⊥,N),hN⟩ = ({((strip_μ ⟨(⊥,N),hN⟩).choose.min' <| μ_nonempty ⟨(⊥,N),hN⟩)} : S₀ R) := sorry

class Coprimary (R : Type) [CommRing R] [IsNoetherianRing R](M : Type) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∀ x : R, (∃ m : M, m ≠ 0 ∧ x • m = 0) → ∃ n : Nat, n > 0 ∧ x^n ∈ Module.annihilator R M

theorem Coprimary_iff  {R : Type} [CommRing R] [IsNoetherianRing R] {M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Coprimary R M ↔ ∃! p, p ∈ associatedPrimes R M := sorry

lemma rmk4d14₂ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := sorry

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μ_Admissible (μ R M) := sorry

open Classical

structure CoprimaryFiltration (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] where
  filtration : ℕ → (ℒ R M)
  monotone : Monotone filtration
  first_eq_bot : filtration 0 = ⊥
  fin_len : ∃ n : ℕ, filtration n = ⊤
  strict_mono : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration i < filtration j
  coprimary : ∀ n : ℕ, n < Nat.find (fin_len) → Coprimary R (filtration (n+1)⧸ (Submodule.submoduleOf (filtration n) (filtration (n+1))))

def lift_quot {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : Submodule R M)
(x : Submodule R (N₂⧸(Submodule.submoduleOf N₁ N₂))) : Submodule R M := by
  exact Submodule.span R <| (Submodule.subtype N₂) '' {m : N₂ | Submodule.Quotient.mk m ∈ x}

lemma lift_quot_middle {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂⧸(Submodule.submoduleOf N₁ N₂))) :
N₁ ≤ lift_quot N₁ N₂ x ∧ lift_quot N₁ N₂ x ≤ N₂ := by
  constructor
  · intro x' hx
    unfold lift_quot
    apply Submodule.subset_span
    simp
    use hN hx
    exact (Submodule.Quotient.mk_eq_zero x).mp (congrArg Submodule.Quotient.mk <| (Submodule.Quotient.mk_eq_zero (N₁.submoduleOf N₂)).mpr hx)
  · unfold lift_quot
    intro x' hx
    refine Submodule.span_le.2 ?_ <| hx
    intro y hy
    simp at hy
    rcases hy with ⟨m,_⟩
    exact m

lemma lift_quot_not_bot {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂⧸(Submodule.submoduleOf N₁ N₂))) (hx : x ≠ ⊥) : lift_quot N₁ N₂ x ≠ N₁:= by
  by_contra hc
  refine hx ?_
  unfold lift_quot at hc
  refine (Submodule.eq_bot_iff x).mpr ?_
  intro r hr

  sorry

noncomputable instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Inhabited (CoprimaryFiltration R M) := by
  have HNFil := (inferInstance : Inhabited (HardarNarasimhanFiltration (μ R M))).default
  refine { default := { filtration := HNFil.filtration, monotone := HNFil.monotone, first_eq_bot := HNFil.first_eq_bot, fin_len := HNFil.fin_len, strict_mono := HNFil.strict_mono, coprimary := ?_ } }
  intro n hn
  have := HNFil.piecewise_semistable n hn
  have ntl : Nontrivial (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) := sorry
  refine Coprimary_iff.2 <| rmk4d14₂.1 <| {semistable := ?_}
  intro x hx
  have := this.semistable ⟨lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x, lift_quot_middle (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone <| Nat.le_succ n) x⟩ <| (by
    apply Subtype.coe_ne_coe.1
    simp only [ne_eq]
    exact lift_quot_not_bot (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone <| Nat.le_succ n) x hx
  )
  convert this
  · sorry
  · simp only [μA, ne_eq]
    congr
    ext u
    constructor
    · intro hu
      simp only [ne_eq, Set.mem_setOf_eq] at *
      rcases hu with ⟨m,⟨hm,hm'⟩⟩
      use ⟨lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) m, lift_quot_middle (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone <| Nat.le_succ n) m⟩
      use ⟨in_TotIntvl _,sorry⟩
      rw [← hm']
      unfold μmax
      congr
      ext v
      constructor
      · intro hv
        simp only [ne_eq, Set.mem_setOf_eq] at *

        sorry
      · sorry
    · sorry


instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Nonempty (CoprimaryFiltration R M) := inferInstance

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Unique (CoprimaryFiltration R M) := sorry


end HardarNarasimhan
