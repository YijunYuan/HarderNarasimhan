import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support

import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Results
import HarderNarasimhan.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.CoprimaryFiltration.Lex'Order
import HarderNarasimhan.Filtration.Results

import HarderNarasimhan.CoprimaryFiltration.Defs

namespace HarderNarasimhan

namespace impl

lemma μ_nonempty {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M]  [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty := by
  intro I
  simp only [Set.toFinset_nonempty]
  have := Submodule.Quotient.nontrivial_of_lt_top (Submodule.submoduleOf I.val.1 I.val.2) <| Classical.byContradiction fun this ↦ (ne_of_lt <| lt_of_lt_of_le I.prop <| Submodule.comap_subtype_eq_top.mp <| not_lt_top_iff.1 this) rfl
  rcases associatedPrimes.nonempty R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_setOf.mpr ?_⟩
  use q, hq

lemma assp {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ u N₃ : Submodule R M} (p : Ideal R)
(m : ↥u ⧸ Submodule.submoduleOf N₁ u)
(hm : p = LinearMap.ker (LinearMap.toSpanSingleton R (↥u ⧸ Submodule.submoduleOf N₁ u) m))
(this : ↑m.out ∈ N₃) :
∃ x, p = LinearMap.ker (LinearMap.toSpanSingleton R (↥N₃ ⧸ Submodule.submoduleOf N₁ N₃) x) := by
  use Submodule.Quotient.mk ⟨m.out, this⟩
  ext y
  constructor
  · intro hy
    rw [hm] at hy
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
    have this': y • (Submodule.Quotient.mk ⟨m.out, this⟩ : ↥N₃ ⧸ Submodule.submoduleOf N₁ N₃) = Submodule.Quotient.mk (y • ⟨m.out, this⟩) := by
      exact rfl
    rw [this']
    simp only [SetLike.mk_smul_mk, Submodule.Quotient.mk_eq_zero]
    unfold Submodule.submoduleOf
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    have : ↑(y • m.out) ∈ N₁ := by
      have : y • m.out ∈ N₁.submoduleOf u := by
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
    have hy : Submodule.Quotient.mk ((y • Quotient.out m): ↥u) = (0 : ↥u ⧸ Submodule.submoduleOf N₁ u) := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact hy
    apply (Submodule.Quotient.mk_eq_zero _).1 at hy
    have : (⟦Quotient.out (y • m)⟧ : ↥u ⧸ Submodule.submoduleOf N₁ u) = ⟦y • Quotient.out m⟧ := by
      simp only [Quotient.out_eq]
      nth_rw 1 [← Quotient.out_eq m]
      exact rfl
    rw [← Quotient.out_eq (y • m), this]
    exact (Submodule.Quotient.mk_eq_zero _).2 hy

lemma assinc {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{N₁ u N₃ : Submodule R M}
(h₁ : N₁ < u) (h₂ : u ≤ N₃)
:
_μ R M ⟨(N₁, u), h₁⟩ ⊆ _μ R M ⟨(N₁, N₃), lt_of_lt_of_le h₁ h₂⟩ := by
  intro i w
  unfold _μ at *
  simp only [Set.mem_setOf_eq] at *
  rcases w with ⟨p,⟨hp1,hp2⟩⟩
  rw [← hp2]
  use p
  simp only [exists_prop, and_true]
  unfold associatedPrimes at *
  simp only [Set.mem_setOf_eq] at *
  unfold IsAssociatedPrime at *
  refine ⟨hp1.1,?_⟩
  simp only [Set.mem_setOf_eq] at hp1
  rcases hp1.2 with ⟨m,hm⟩
  refine assp p m hm <| (Submodule.Quotient.mk_eq_zero N₃).mp ?_
  aesop


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
    exact Set.toFinset_subset_toFinset.mpr <| assinc (lt_of_le_of_ne hu1.1.1 hu1.2) hu1.1.2

lemma mem_support_of_mem_associatedPrimes {R : Type} [CommRing R]
{M : Type} [AddCommGroup M] [Module R M] {x : Ideal R}:
(hx : x ∈ associatedPrimes R M) →  {asIdeal := x, isPrime := hx.out.1} ∈  Module.support R M := by
  intro hx
  apply Module.mem_support_iff_exists_annihilator.2
  rcases hx with ⟨p,m,hpm⟩
  use m
  simp only [hpm]
  intro z hz
  exact (Submodule.mem_annihilator_span_singleton m z).mp hz

lemma TBA' {R : Type} [CommRing R]
{M : Type} [AddCommGroup M] [Module R M]
(N₁ N₂ N₃ : Submodule R M) (h : N₁ ≤ N₂)
: Module.support R (N₃⧸ N₂.submoduleOf N₃) ⊆ Module.support R (N₃⧸ N₁.submoduleOf N₃) := by
  intro p hp
  simp [Module.mem_support_iff_exists_annihilator] at *
  rcases hp with ⟨m,hm⟩
  use Submodule.Quotient.mk m.out
  intro z hz
  have : z • (Submodule.Quotient.mk m.out : ↥N₃ ⧸ N₁.submoduleOf N₃)= 0 := by exact
    (Submodule.mem_annihilator_span_singleton (Submodule.Quotient.mk (Quotient.out m)) z).mp hz
  have : z ∈ (Submodule.span R {m}).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton]
    rw [← Submodule.Quotient.mk_smul] at this
    apply (Submodule.Quotient.mk_eq_zero _).1 at this
    have this' : z • m = Submodule.Quotient.mk (z • m).out := by
      unfold Submodule.Quotient.mk Quotient.mk''
      rw [Quotient.out_eq]
    rw [this']
    apply (Submodule.Quotient.mk_eq_zero _).2
    have this' : z • m.out - (z • m).out ∈ N₂.submoduleOf N₃ := by
      apply (Submodule.Quotient.mk_eq_zero _).1
      simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      unfold Submodule.Quotient.mk Quotient.mk''
      rw [Quotient.out_eq, Quotient.out_eq, sub_self]
    exact (Submodule.sub_mem_iff_right (N₂.submoduleOf N₃) (h this)).mp this'
  exact hm this

lemma min_associated_prime_iff_min_supp {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : PrimeSpectrum R} :
Minimal (fun J ↦ J ∈ associatedPrimes R M) I.asIdeal ↔ Minimal (fun J ↦ J ∈ Module.support R M) I := by
  sorry

lemma exists_minimal_prime_contained_supp {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ q : PrimeSpectrum R, q ∈ Module.support R M → ∃ p : PrimeSpectrum R, Minimal (fun J ↦ J ∈ Module.support R M) p ∧ p ≤ q := by sorry

lemma prop3d12p1 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
(N'' : ℒ R M) (ha1 : InIntvl I N'') (ha2 : N'' ≠ I.val.2) : ∀ q : Ideal R, (hq : q ∈ associatedPrimes R (I.val.2⧸N''.submoduleOf I.val.2)) → {asIdeal := q, isPrime := hq.out.1 } ≥ (((_μ R M) I).toFinset.min' (μ_nonempty I)) := by
  intro q hq
  have hq' := TBA' I.val.1 N'' I.val.2 (ha1.1) <| mem_support_of_mem_associatedPrimes hq
  obtain ⟨r,hr,hr'⟩ := exists_minimal_prime_contained_supp {asIdeal := q, isPrime := hq.out.1 } hq'
  rw [← min_associated_prime_iff_min_supp] at hr
  have := (((_μ R M) I).toFinset.min'_le) r (by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    use r.asIdeal, hr.1
    )
  exact le_trans this <|  toLinearExtension.monotone' hr'

noncomputable abbrev ker_of_quot_comp_localization {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
: ℒ R M := by
  let f1 := LocalizedModule.mkLinearMap (((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl (I.val.2⧸I.val.1.submoduleOf I.val.2)
  let f2 : I.val.2 →ₗ[R] (I.val.2⧸I.val.1.submoduleOf I.val.2) :=
    { toFun := fun x : I.val.2 ↦ (I.val.1.submoduleOf I.val.2).mkQ x,
      map_add' := fun x y => rfl,
      map_smul' := fun r x => rfl }
  exact Submodule.map I.val.2.subtype (LinearMap.ker (f1 ∘ₗ f2))

lemma prop3d12p2 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
(N'' : ℒ R M) (ha1 : InIntvl I N'') (ha2 : N'' ≠ I.val.2) : @LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I} (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset   := by
  have : @LE.le (S₀ R) Preorder.toLE {(_μ R M I).toFinset.min' <| μ_nonempty I} {(_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩} := by
    rw [← S₀_order.2]
    have this' : ((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).asIdeal ∈ associatedPrimes R (↥I.val.2 ⧸ Submodule.submoduleOf N'' I.val.2) := by
      simp only [Set.mem_setOf_eq]
      have := ((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).out
      simp only [Finset.mem_val, Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      exact hp1
    exact prop3d12p1 I N'' ha1 ha2 (((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).asIdeal) this'
  refine le_trans this ?_
  apply S₀_order.1
  simp only [Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
  exact Set.mem_toFinset.mp <| (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩

lemma TBA {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
:
(
InIntvl I (ker_of_quot_comp_localization I) ∧ (ker_of_quot_comp_localization I) ≠ I.val.2
) ∧
associatedPrimes R (I.val.2⧸(ker_of_quot_comp_localization I).submoduleOf I.val.2) = {(((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal}
:= sorry

lemma prop3d12 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I = ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R) := by
  intro I
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  unfold μA
  simp only [noname, ne_eq]
  unfold μ
  simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  have res1 : (coe' {(_μ R M I).toFinset.min' (μ_nonempty I)} : S R) ∈ {x | ∃ a, ∃ (h : InIntvl I a ∧ ¬a = I.val.2), coe' (_μ R M ⟨(a, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩).toFinset = x} := by
    simp only [exists_prop, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq]
    use ker_of_quot_comp_localization I
    constructor
    · conv_lhs => unfold _μ
      simp only [(TBA I).2, Set.mem_singleton_iff, exists_prop_eq, Set.setOf_eq_eq_singleton',
        Set.toFinset_singleton, Finset.singleton_inj]
      rfl
    · constructor
      · constructor
        · unfold ker_of_quot_comp_localization
          simp only [Submodule.mkQ_apply]
          intro z hz
          simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk,
            AddHom.coe_mk, Function.comp_apply, Submodule.subtype_apply, Subtype.exists,
            exists_and_right, exists_eq_right]
          use (le_of_lt I.prop) hz
          have : Submodule.Quotient.mk ⟨z, (Iff.of_eq (Eq.refl (z ∈ I.val.2))).mpr (le_of_lt (Subtype.prop I) hz) ⟩ = (0 : ↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2) := by
            simp only [Submodule.Quotient.mk_eq_zero]
            exact hz
          simp only [this]
          exact rfl
        · unfold ker_of_quot_comp_localization
          simp only [Submodule.map_subtype_le]
      · by_contra hc
        have := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
        simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
        rcases this with ⟨p,⟨hp1,hp2⟩⟩
        apply mem_support_of_mem_associatedPrimes at hp1
        have hp1 := hp1.out
        have : LinearMap.ker (LocalizedModule.mkLinearMap (((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl (I.val.2⧸I.val.1.submoduleOf I.val.2)) ≠ ⊤ := by
          by_contra hc
          apply LocalizedModule.subsingleton_iff_ker_eq_top.2 at hc
          rw [hp2] at hp1
          exact false_of_nontrivial_of_subsingleton (LocalizedModule ((_μ R M I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2))



        sorry
  apply IsLeast.csInf_eq
  refine ⟨res1,?_⟩
  apply mem_lowerBounds.2
  intro N hN
  rcases hN with ⟨a,ha1,ha2⟩
  rw [← ha2]
  simp only [OrderEmbedding.le_iff_le]
  exact prop3d12p2 I a ha1.1 ha1.2


end impl

end HarderNarasimhan
