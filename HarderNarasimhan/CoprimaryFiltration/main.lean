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
import HarderNarasimhan.CoprimaryFiltration.Lex'Order

namespace HardarNarasimhan

abbrev S₀ (R : Type) [CommRing R] [IsNoetherianRing R] := Finset (LinearExtension (PrimeSpectrum R))

noncomputable instance (priority:=114514) {R : Type} [CommRing R] [IsNoetherianRing R]: LinearOrder (S₀ R) :=
  (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose

noncomputable instance (priority:=114513) {R : Type} [CommRing R] [IsNoetherianRing R]: PartialOrder (S₀ R) := instLinearOrderS₀.toPartialOrder
noncomputable instance (priority:=114512) {R : Type} [CommRing R] [IsNoetherianRing R]: LE (S₀ R) where
  le := instLinearOrderS₀.le

lemma S₀_order {R : Type} [CommRing R] [IsNoetherianRing R]:
(∀ A B : S₀ R, A ⊆ B → A ≤ B) ∧
∀ a b : LinearExtension (PrimeSpectrum R), a ≤ b ↔ ({a} : (S₀ R)) ≤ ({b} : (S₀ R)) :=
  (Lex'Order.Lex'Order_prop (LinearExtension (PrimeSpectrum R))).choose_spec

abbrev S (R : Type) [CommRing R] [IsNoetherianRing R] := @DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

abbrev ℒ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:= Submodule R M

noncomputable abbrev μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R) := fun I ↦ coe'.toFun <| @Set.toFinset (LinearExtension (PrimeSpectrum R))
({ {asIdeal := p, isPrime := h.out.1} | (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) })
 <| (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

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
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := by
  intro I
  unfold μmax
  apply IsGreatest.csSup_eq
  unfold IsGreatest
  constructor
  · simp only [ne_eq, Set.mem_setOf_eq]
    use I.val.2
    use ⟨⟨le_of_lt I.prop,le_rfl⟩,ne_of_lt I.prop⟩
  · apply mem_upperBounds.2
    intro x hx
    simp only [ne_eq, Set.mem_setOf_eq] at hx
    rcases hx with ⟨u,⟨hu1,hu2⟩⟩
    rw [← hu2]
    unfold μ
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      OrderEmbedding.le_iff_le]
    apply S₀_order.1
    intro w hw
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hw
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    rcases hw with ⟨p,⟨hp,hp'⟩⟩
    rw [← hp']
    use p
    simp only [exists_prop, and_true]
    apply AssociatePrimes.mem_iff.mpr
    apply AssociatePrimes.mem_iff.1 at hp
    unfold IsAssociatedPrime at *
    refine ⟨hp.1,?_⟩
    rcases hp.2 with ⟨m,hm⟩
    have : ↑m.out ∈ I.val.2 := by
      have := hu1.1.2
      refine (Submodule.Quotient.mk_eq_zero I.val.2).mp ?_
      aesop
    use Submodule.Quotient.mk ⟨m.out, this⟩
    ext y
    constructor
    · intro hy
      rw [hm] at hy
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
      have this': y • (Submodule.Quotient.mk ⟨m.out, this⟩ : ↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2) = Submodule.Quotient.mk (y • ⟨m.out, this⟩) := by
        exact rfl
      rw [this']
      simp only [SetLike.mk_smul_mk, Submodule.Quotient.mk_eq_zero]
      unfold Submodule.submoduleOf
      simp only [Submodule.mem_comap, Submodule.subtype_apply]
      have : ↑(y • m.out) ∈ I.val.1 := by
        have : y • m.out ∈ I.val.1.submoduleOf u := by
          apply (Submodule.Quotient.mk_eq_zero _).1
          simp only [Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk
          simp only [Quotient.out_eq, hy]
        exact this
      exact this
    · intro hy
      rw [hm]
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
      apply (Submodule.Quotient.mk_eq_zero _).1 at hy
      simp only [SetLike.mk_smul_mk] at hy
      have hy : Submodule.Quotient.mk ((y • Quotient.out m): ↥u) = (0 : ↥u ⧸ Submodule.submoduleOf I.val.1 u) := by
        apply (Submodule.Quotient.mk_eq_zero _).2
        exact hy
      apply (Submodule.Quotient.mk_eq_zero _).1 at hy
      have : (⟦Quotient.out (y • m)⟧ : ↥u ⧸ Submodule.submoduleOf I.val.1 u) = ⟦y • Quotient.out m⟧ := by
        simp only [Quotient.out_eq]
        nth_rw 1 [← Quotient.out_eq m]
        exact rfl
      rw [← Quotient.out_eq (y • m), this]
      exact (Submodule.Quotient.mk_eq_zero _).2 hy

instance prop_3_11 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := by
  refine { convex := fun x y _ _ hxy ↦ ?_ }
  unfold μ
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.le_iff_le]

  sorry

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
(x : Submodule R (N₂⧸(N₁.submoduleOf N₂))) : Submodule R M :=
  Submodule.map N₂.subtype (Submodule.comap (N₁.submoduleOf N₂).mkQ x)

lemma lift_quot_middle {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂⧸(N₁.submoduleOf N₂))) :
N₁ ≤ lift_quot N₁ N₂ x ∧ lift_quot N₁ N₂ x ≤ N₂ := by
  constructor
  · intro x' hx
    unfold lift_quot
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right]
    use hN hx
    convert Submodule.zero_mem x
    simp
    exact hx
  · unfold lift_quot
    intro x' hx
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.subtype_apply,
      Subtype.exists, exists_and_right, exists_eq_right] at hx
    exact hx.choose

lemma lift_quot_not_bot {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M) (hN : N₁ ≤ N₂)
(x : Submodule R (N₂⧸(N₁.submoduleOf N₂))) (hx : x ≠ ⊥) : lift_quot N₁ N₂ x ≠ N₁:= by
  by_contra hc
  refine hx ?_
  unfold lift_quot at hc
  refine (Submodule.eq_bot_iff x).mpr ?_
  intro r hr
  rcases (Quotient.exists_rep r) with ⟨rtilde,hrtilde⟩
  have : N₂.subtype rtilde ∈ N₁ := by
    rw [← hc]
    simp
    convert hr
  rw [← hrtilde]
  apply (Submodule.Quotient.mk_eq_zero (N₁.submoduleOf N₂)).2
  exact this

noncomputable instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Inhabited (CoprimaryFiltration R M) := by
  have HNFil := (inferInstance : Inhabited (HardarNarasimhanFiltration (μ R M))).default
  refine { default := { filtration := HNFil.filtration, monotone := HNFil.monotone, first_eq_bot := HNFil.first_eq_bot, fin_len := HNFil.fin_len, strict_mono := HNFil.strict_mono, coprimary := ?_ } }
  intro n hn
  have := HNFil.piecewise_semistable n hn
  have ntl : Nontrivial (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) := by
    apply Submodule.Quotient.nontrivial_of_lt_top
    apply lt_top_iff_ne_top.2
    by_contra hc
    have h' : ∀ x ∈ HNFil.filtration (n + 1), x ∈ HNFil.filtration n := by
      intro x hx
      have : ⟨x,hx⟩ ∈ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)) := hc ▸ Submodule.mem_top
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at this
      exact this
    exact (not_lt_of_le h') <| HNFil.strict_mono n (n+1) (lt_add_one n) hn
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
      use ⟨in_TotIntvl _,by
        by_contra hc
        refine hm.2 ?_
        apply Subtype.coe_inj.2 at hc
        simp only at hc
        simp [lift_quot] at hc
        have : Submodule.comap (Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))).mkQ m = ⊤ := by
          have : ↑(⊤: Interval ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n + 1) (lt_add_one n) hn⟩) = Submodule.map (Submodule.subtype (HNFil.filtration (n + 1))) ⊤ := by
            simp only [Submodule.map_top, Submodule.range_subtype]
            exact rfl
          exact Submodule.map_injective_of_injective (Submodule.injective_subtype (HNFil.filtration (n + 1))) <| this ▸ hc
        refine Submodule.comap_injective_of_surjective ?_ this
        exact Submodule.mkQ_surjective (Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)))
        ⟩
      rw [← hm']
      unfold μmax
      congr
      ext v
      constructor
      · intro hv
        simp only [ne_eq, Set.mem_setOf_eq] at *
        rcases hv with ⟨w,⟨hw,hw'⟩⟩
        use Submodule.map (Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))).mkQ <| w.val.submoduleOf (HNFil.filtration (n + 1))
        refine ⟨⟨?_,?_⟩,?_⟩
        · constructor
          · simp only
            have hw := hw.1.1
            apply Subtype.coe_le_coe.2 at hw
            simp at hw
            unfold lift_quot at hw
            exact Submodule.le_map_of_comap_le_of_surjective (Submodule.mkQ_surjective (Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)))) <| Submodule.map_le_iff_le_comap.1 hw
          · exact le_top
        · by_contra hc
          refine hw.2 ?_
          rw [hc]
          apply Subtype.coe_inj.1
          simp only
          unfold lift_quot
          simp [Submodule.map_comap_eq]
          have h1 : Submodule.map (Submodule.subtype (HNFil.filtration (n + 1))) (Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) = HNFil.filtration n := by
            simp only [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right]
            exact le_trans w.prop.1 w.prop.2
          have h2: Submodule.map (Submodule.subtype (HNFil.filtration (n + 1))) (Submodule.submoduleOf (↑w) (HNFil.filtration (n + 1))) = ↑w := by
            simp only [Submodule.submoduleOf, Submodule.map_comap_subtype, inf_eq_right]
            exact w.prop.2
          rw [h1, h2]
          exact sup_eq_right.2 <| w.prop.1
        · rw [← hw']
          simp [lift_quot,Resμ]

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
