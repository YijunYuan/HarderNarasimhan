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
import HarderNarasimhan.OrderTheory.DedekindMacNeilleCompletion
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Filtration.Results
import HarderNarasimhan.OrderTheory.Lex'Order
import HarderNarasimhan.CoprimaryFiltration.AdmittedResults

import HarderNarasimhan.CoprimaryFiltration.Defs

namespace HarderNarasimhan

namespace impl

lemma μ_nonempty {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M]  [Module.Finite R M]:
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty := by
  intro I
  simp only [Set.toFinset_nonempty]
  have := Submodule.Quotient.nontrivial_of_lt_top (Submodule.submoduleOf I.val.1 I.val.2) <| Classical.byContradiction fun this ↦ (ne_of_lt <| lt_of_lt_of_le I.prop <| Submodule.comap_subtype_eq_top.mp <| not_lt_top_iff.1 this) rfl
  rcases associatedPrimes.nonempty R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2)) with ⟨q,hq⟩
  refine ⟨{ asIdeal := q, isPrime := hq.out.1 },Set.mem_setOf.mpr ?_⟩
  use q, hq

lemma assp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
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

lemma assinc {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
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


lemma noname {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μmax (μ R M) I = (μ R M) I := by
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


instance prop3d11 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := by
  refine { convex := fun x y _ _ hxy ↦ ?_ }
  unfold μ
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.le_iff_le]
  refine S₀_order.1 (_μ R M ⟨(x ⊓ y, x), inf_lt_left.mpr hxy⟩).toFinset (_μ R M ⟨(y, x ⊔ y), right_lt_sup.mpr hxy⟩).toFinset (Set.toFinset_subset_toFinset.mpr ?_)
  unfold _μ
  intro w hw
  simp only [Set.mem_setOf_eq] at *
  rcases hw with ⟨p,⟨hp1,hp2⟩⟩
  use p
  simp only [hp2, exists_prop, and_true]
  apply AssociatePrimes.mem_iff.2
  apply AssociatePrimes.mem_iff.1 at hp1
  refine ⟨hp1.1,?_⟩
  rcases hp1.2 with ⟨m,hm⟩
  use (LinearMap.quotientInfEquivSupQuotient _ _).toFun m
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  rw [hm]
  ext r
  have := Eq.symm (LinearEquiv.map_smul (LinearMap.quotientInfEquivSupQuotient x y) r m)
  constructor
  · intro h
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
    simp only [this, h, map_zero]
  · intro h
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
    rw [this] at h
    exact (LinearEquiv.map_eq_zero_iff (LinearMap.quotientInfEquivSupQuotient x y)).mp h

lemma mem_support_of_mem_associatedPrimes {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M] {x : Ideal R}:
(hx : x ∈ associatedPrimes R M) →  {asIdeal := x, isPrime := hx.out.1} ∈  Module.support R M := by
  intro hx
  apply Module.mem_support_iff_exists_annihilator.2
  rcases hx with ⟨p,m,hpm⟩
  use m
  simp only [hpm]
  intro z hz
  exact (Submodule.mem_annihilator_span_singleton m z).mp hz

lemma support_quotient_mono {R : Type*} [CommRing R]
{M : Type*} [AddCommGroup M] [Module R M]
(N₁ N₂ N₃ : Submodule R M) (h : N₁ ≤ N₂) :
  Module.support R (N₃⧸ N₂.submoduleOf N₃) ⊆ Module.support R (N₃⧸ N₁.submoduleOf N₃) := by
  intro p hp
  simp only [Module.mem_support_iff_exists_annihilator] at *
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



lemma exists_minimal_prime_contained_supp {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
∀ q : PrimeSpectrum R, q ∈ Module.support R M → ∃ p : PrimeSpectrum R, Minimal (fun J ↦ J ∈ Module.support R M) p ∧ p ≤ q := by
  intro q hq
  rcases Ideal.exists_minimalPrimes_le <| Module.mem_support_iff_of_finite.1 hq with ⟨r,hr⟩
  use ⟨r, hr.1.out.1.1⟩
  refine ⟨?_,hr.2⟩
  simp only [Module.mem_support_iff_of_finite]
  exact ⟨hr.1.out.1.2, fun y hy1 hy2 ↦ hr.1.out.2 ⟨y.isPrime,hy1⟩ hy2⟩

lemma prop3d12p1 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
(N'' : ℒ R M) (ha1 : InIntvl I N'') :
∀ q : Ideal R, (hq : q ∈ associatedPrimes R (I.val.2⧸N''.submoduleOf I.val.2)) → {asIdeal := q, isPrime := hq.out.1 } ≥ (((_μ R M) I).toFinset.min' (μ_nonempty I)) := by
  intro q hq
  have hq' := support_quotient_mono I.val.1 N'' I.val.2 (ha1.1) <| mem_support_of_mem_associatedPrimes hq
  obtain ⟨r,hr,hr'⟩ := exists_minimal_prime_contained_supp {asIdeal := q, isPrime := hq.out.1 } hq'
  rw [← AdmittedResults.min_associated_prime_iff_min_supp] at hr
  have := (((_μ R M) I).toFinset.min'_le) r (by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    use r.asIdeal, hr.1
    )
  exact le_trans this <|  toLinearExtension.monotone' hr'

lemma prop3d12p2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
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
    exact prop3d12p1 I N'' ha1 (((_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min' <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).asIdeal) this'
  refine le_trans this ?_
  apply S₀_order.1
  simp only [Set.subset_toFinset, Finset.coe_singleton, Set.singleton_subset_iff]
  exact Set.mem_toFinset.mp <| (_μ R M ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩).toFinset.min'_mem <| μ_nonempty ⟨(N'', I.val.2), lt_of_le_of_ne ha1.2 ha2⟩

noncomputable abbrev f1 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) := LocalizedModule.mkLinearMap (((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl (I.val.2⧸I.val.1.submoduleOf I.val.2)

abbrev f2 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) : I.val.2 →ₗ[R] (I.val.2⧸I.val.1.submoduleOf I.val.2) := { toFun := fun x : I.val.2 ↦ (I.val.1.submoduleOf I.val.2).mkQ x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

noncomputable abbrev ker_of_quot_comp_localization {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2})
: ℒ R M :=
Submodule.map I.val.2.subtype (LinearMap.ker ((f1 I) ∘ₗ (f2 I)))

lemma submoduleOf_map_subtype {R : Type*} [CommRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M]
(N : Submodule R M) (N' : Submodule R ↥N): N' = (Submodule.map (N.subtype) N').submoduleOf N := by
  ext z
  constructor
  · intro hz
    use z
    simp only [SetLike.mem_coe, Submodule.subtype_apply, and_true]
    exact hz
  · intro hz
    rcases hz with ⟨y,hy1,hy2⟩
    simp only [Submodule.subtype_apply, SetLike.coe_eq_coe] at hy2
    exact hy2 ▸ hy1

lemma koqcl_iso {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
∃ _ : LinearEquiv (RingHom.id R) (I.val.2⧸((ker_of_quot_comp_localization I).submoduleOf I.val.2)) ((I.val.2⧸(I.val.1.submoduleOf I.val.2))⧸ (LinearMap.ker (f1 I))), True := by
  unfold ker_of_quot_comp_localization
  have := (@Submodule.quotientQuotientEquivQuotient R  (I.val.2) _ _ _ (I.val.1.submoduleOf I.val.2) ((Submodule.map (Submodule.subtype I.val.2) (LinearMap.ker (f1 I ∘ₗ f2 I))).submoduleOf I.val.2) (by
    intro z hz
    rw [← submoduleOf_map_subtype I.val.2 (LinearMap.ker (f1 I ∘ₗ f2 I))]
    rw [LinearMap.mem_ker]
    have : (f2 I) z = 0 := by
      unfold f2
      simp only [Submodule.mkQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Submodule.Quotient.mk_eq_zero]
      exact hz
    rw [LinearMap.comp_apply,this]
    rfl)).symm
  have t : Submodule.map (Submodule.submoduleOf I.val.1 I.val.2).mkQ
      ((Submodule.map (Submodule.subtype I.val.2) (LinearMap.ker (f1 I ∘ₗ f2 I))).submoduleOf I.val.2) = LinearMap.ker (f1 I) := by
      ext z
      simp only [Submodule.mem_map, Submodule.mkQ_apply, Subtype.exists, LinearMap.mem_ker]
      constructor
      · intro hz
        rcases hz with ⟨y,hy1,hy2,hy3⟩
        have hy2 : y ∈ Submodule.map (Submodule.subtype I.val.2) (LinearMap.ker (f1 I ∘ₗ f2 I)) := hy2
        simp only [Submodule.mem_map, LinearMap.mem_ker] at hy2
        rcases hy2 with ⟨w,hw1,hw2⟩
        have : Submodule.Quotient.mk ⟨y, hy1⟩ = (f2 I) w := by aesop
        rw [← hy3, this]
        exact hw1
      · intro hz
        use z.out.val, Submodule.coe_mem z.out
        simp only [Subtype.coe_eta]
        constructor
        · have : z.out ∈ LinearMap.ker (f1 I ∘ₗ f2 I) := by
            simp only [LinearMap.mem_ker]
            have : (f2 I) z.out = z := by
              unfold f2
              simp only [Submodule.mkQ_apply, LinearMap.coe_mk, AddHom.coe_mk]
              unfold Submodule.Quotient.mk Quotient.mk''
              rw [Quotient.out_eq]
            rw [← this] at hz
            exact hz
          convert this
          rw [← submoduleOf_map_subtype]
        · unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
  rw [t] at this
  use this

lemma associated_primes_quot_koqcl {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) :
associatedPrimes R (I.val.2⧸(ker_of_quot_comp_localization I).submoduleOf I.val.2) = {(((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal}
:= by
  rcases koqcl_iso I with ⟨h, _⟩
  rw [LinearEquiv.AssociatedPrimes.eq h]
  have := AdmittedResults.bourbaki_elements_math_alg_comm_chIV_sec1_no2_prop6 ((((_μ R M) I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl) (LinearMap.ker (f1 I))
  simp only [iff_true] at this
  rw [this.2]
  ext q
  constructor
  · intro hq
    simp only [Set.mem_setOf_eq] at hq
    simp only [Set.mem_singleton_iff]
    have := ((_μ R M) I).toFinset.min'_le {asIdeal := q, isPrime := hq.1.out.1} (by
      simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      use q, hq.1)
    simp only [eq_of_le_of_le this <| toLinearExtension.monotone' <| Set.diff_eq_empty.mp hq.2]
  · intro hq
    simp only [Set.sdiff_sep_self, Set.mem_singleton_iff,
      Set.mem_setOf_eq] at *
    rw [hq]
    constructor
    · have := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨_,⟨hp1,hp2⟩⟩
      exact hp2 ▸ hp1
    · unfold Ideal.primeCompl
      simp only [Submodule.carrier_eq_coe, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
        Set.inter_compl_self]

lemma prop3d12 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I = ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R) := by
  intro I
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  unfold μA
  simp only [noname, ne_eq]
  unfold μ
  simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  have res1 : (OrderTheory.coe' {(_μ R M I).toFinset.min' (μ_nonempty I)} : S R) ∈ {x | ∃ a, ∃ (h : InIntvl I a ∧ ¬a = I.val.2), OrderTheory.coe' (_μ R M ⟨(a, I.val.2), lt_of_le_of_ne h.1.2 h.2⟩).toFinset = x} := by
    simp only [exists_prop, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq]
    use ker_of_quot_comp_localization I
    constructor
    · conv_lhs => unfold _μ
      simp only [associated_primes_quot_koqcl I, Set.mem_singleton_iff, exists_prop_eq, Set.setOf_eq_eq_singleton',
        Set.toFinset_singleton, Finset.singleton_inj]
      rfl
    · constructor
      · constructor
        · unfold ker_of_quot_comp_localization
          intro z hz
          simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk,
            AddHom.coe_mk, Function.comp_apply, Submodule.subtype_apply, Subtype.exists,
            exists_and_right, exists_eq_right]
          use (le_of_lt I.prop) hz
          have : Submodule.Quotient.mk ⟨z, (Iff.of_eq (Eq.refl (z ∈ I.val.2))).mpr (le_of_lt (Subtype.prop I) hz) ⟩ = (0 : ↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2) := by
            simp only [Submodule.Quotient.mk_eq_zero]
            exact hz
          simp only [Submodule.mkQ_apply, this, LocalizedModule.mkLinearMap_apply,
            LocalizedModule.zero_mk]
        · unfold ker_of_quot_comp_localization
          simp only [Submodule.map_subtype_le]
      · by_contra hc
        have := (((_μ R M) I).toFinset.min'_mem (μ_nonempty I))
        simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
        rcases this with ⟨p,⟨hp1,hp2⟩⟩
        apply mem_support_of_mem_associatedPrimes at hp1
        have hp1 := hp1.out
        have : LinearMap.ker (f1 I) ≠ ⊤ := by
          by_contra hc
          apply LocalizedModule.subsingleton_iff_ker_eq_top.2 at hc
          rw [hp2] at hp1
          exact false_of_nontrivial_of_subsingleton (LocalizedModule ((_μ R M I).toFinset.min' (μ_nonempty I)).asIdeal.primeCompl (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2))
        have : ∃ m : (↥I.val.2 ⧸ Submodule.submoduleOf I.val.1 I.val.2), (f1 I) m ≠ 0 := by
          by_contra hc
          push_neg at hc
          have this' : LinearMap.ker (f1 I) = ⊤ := Submodule.ext fun z ↦ { mp := fun hz ↦ True.intro, mpr := fun hz ↦ hc z }
          exact this this'
        rcases this with ⟨m,hm⟩
        unfold ker_of_quot_comp_localization at hc
        have this' : (f1 I ∘ₗ f2 I) m.out = 0 := by
          have : m.out.val ∈ Submodule.map (Submodule.subtype I.val.2) (LinearMap.ker (f1 I ∘ₗ f2 I)) := by
            have := m.out.prop
            conv at this =>
              arg 1; simp only [← hc]
            exact this
          simp only [ne_eq, LinearMap.ker_eq_top, LocalizedModule.mkLinearMap_apply,
            Submodule.mem_map, LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk,
            Submodule.mkQ_apply, AddHom.coe_mk, Function.comp_apply, Submodule.subtype_apply,
            SetLike.coe_eq_coe, exists_eq_right] at *
          exact this
        unfold f2 at this'
        simp only [Submodule.mkQ_apply, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
          Function.comp_apply] at this'
        unfold Submodule.Quotient.mk Quotient.mk'' at this'
        rw [Quotient.out_eq] at this'
        exact hm this'
  apply IsLeast.csInf_eq
  refine ⟨res1,?_⟩
  apply mem_lowerBounds.2
  intro N hN
  rcases hN with ⟨a,ha1,ha2⟩
  rw [← ha2]
  simp only [OrderEmbedding.le_iff_le]
  exact prop3d12p2 I a ha1.1 ha1.2

instance prop3d13₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : WellFoundedGT (ℒ R M) := wellFoundedGT

instance prop3d13₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μA_DescendingChainCondition (μ R M) where
  μ_dcc := by
    intro N x hx1 hx2
    by_contra hc
    simp only [not_exists, not_le] at hc
    simp only [prop3d12, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      OrderEmbedding.le_iff_le, not_le] at hc
    have hc := fun w ↦ S₀_order'.mpr (by
      simpa only [OrderEmbedding.lt_iff_lt] using (hc w)
      )
    have s1 : ∀ i, ((_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min' <| μ_nonempty ⟨(N, x i), hx1 i⟩).asIdeal ∈ associatedPrimes R ((x i)⧸(Submodule.submoduleOf N (x i))) := by
      intro i
      have := (_μ R M ⟨(N, x i), hx1 i⟩).toFinset.min'_mem (μ_nonempty ⟨(N, x i), hx1 i⟩)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      exact hp1
    have s2 : ∀ i, associatedPrimes R (↥(x i) ⧸ Submodule.submoduleOf N (x i)) ⊆ associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0)) := by
      intro i w hw'
      unfold associatedPrimes at *
      simp only [Set.mem_setOf_eq] at *
      unfold IsAssociatedPrime at *
      refine ⟨hw'.1,?_⟩
      rcases hw'.2 with ⟨m,hm⟩
      have : ↑(Quotient.out m) ∈ x 0 :=
        (if hi : i = 0 then hi ▸ le_rfl
        else le_of_lt (strictAnti_nat_of_succ_lt hx2 <| Nat.zero_lt_of_ne_zero hi)) <| Submodule.coe_mem (Quotient.out m)
      exact assp w m hm this
    have : (associatedPrimes R (↥(x 0) ⧸ Submodule.submoduleOf N (x 0))).Infinite := by
      refine Set.infinite_of_injective_forall_mem ?_ <| fun i ↦ s2 i (s1 i)
      intro a b hab
      by_contra!
      have help : ∀ A B : LinearExtension (PrimeSpectrum R), A.asIdeal = B.asIdeal → A = B :=
            fun A B h ↦ id (PrimeSpectrum.ext (Ideal.ext fun t ↦ Eq.to_iff (congrFun (congrArg Membership.mem h) t)))
      cases' ne_iff_lt_or_gt.1 this with this this
      · have := strictMono_nat_of_lt_succ hc this
        rw [help ((_μ R M ⟨(N, x a), hx1 a⟩).toFinset.min' (μ_nonempty ⟨(N, x a), hx1 a⟩)) ((_μ R M ⟨(N, x b), hx1 b⟩).toFinset.min' (μ_nonempty ⟨(N, x b), hx1 b⟩)) hab] at this
        exact (lt_self_iff_false _).1 this
      · have := strictMono_nat_of_lt_succ hc this
        rw [help ((_μ R M ⟨(N, x a), hx1 a⟩).toFinset.min' (μ_nonempty ⟨(N, x a), hx1 a⟩)) ((_μ R M ⟨(N, x b), hx1 b⟩).toFinset.min' (μ_nonempty ⟨(N, x b), hx1 b⟩)) hab] at this
        exact (lt_self_iff_false _).1 this
    exact this <| associatedPrimes.finite R ((↥(x 0) ⧸ Submodule.submoduleOf N (x 0)))

lemma rmk4d14₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨(⊥,N),hN⟩ = ({(((_μ R M) ⟨(⊥,⊤),bot_lt_top⟩).toFinset.min' (μ_nonempty ⟨(⊥,⊤),bot_lt_top⟩))} : S₀ R) := by
  constructor
  · intro hst
    intro N hN
    have hst := hst.semistable N (bot_lt_iff_ne_bot.1 hN)
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    rw [prop3d12 ⟨(⊥,N),hN⟩, prop3d12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩] at hst
    rw [prop3d12 ⟨(⊥,N),hN⟩]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, gt_iff_lt,
      OrderEmbedding.lt_iff_lt, not_lt] at hst
    apply (S₀_order.2 _ _).2 at hst
    exact eq_of_le_of_le hst <| Finset.min'_subset (μ_nonempty ⟨(⊥, N), hN⟩) <| Set.toFinset_subset_toFinset.mpr <| assinc hN fun ⦃x⦄ a ↦ by trivial
  · intro h
    refine { semistable := ?_ }
    intro N hN
    have h := h N (bot_lt_iff_ne_bot.2 hN)
    have t1 := prop3d12 ⟨(⊥,N),bot_lt_iff_ne_bot.2 hN⟩
    have t2 := prop3d12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩
    rw [prop3d12 ⟨(⊥,N),bot_lt_iff_ne_bot.2 hN⟩] at h
    simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj] at h
    rw [t1,t2]
    simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, gt_iff_lt,
      OrderEmbedding.lt_iff_lt, not_lt, ge_iff_le]
    apply (S₀_order.2 _ _).1
    rw [h]

set_option maxHeartbeats 0
lemma rmk4d14₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [rmk4d14₁]
  constructor
  · intro h
    have := prop3d12 (⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩)
    use ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min' <| μ_nonempty ⟨(⊥, ⊤), bot_lt_top⟩).asIdeal
    constructor
    · simp only
      have := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_mem <| μ_nonempty ⟨(⊥, ⊤), bot_lt_top⟩
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      simp
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := Submodule.quotEquivOfEqBot (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
      exact LinearEquiv.trans t1 Submodule.topEquiv
    · intro J hJ
      by_contra hc
      have := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_le ⟨J,hJ.out.1⟩ (by
        simp only [Set.mem_toFinset, Set.mem_setOf_eq]
        use J
        simp only [exists_prop, and_true]
        convert hJ
        refine LinearEquiv.AssociatedPrimes.eq <| ?_
        have t1 := Submodule.quotEquivOfEqBot (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
        exact LinearEquiv.trans t1 Submodule.topEquiv
        )
      simp only at this
      unfold associatedPrimes IsAssociatedPrime at hJ
      simp only [Set.mem_setOf_eq] at hJ
      rcases hJ.2 with ⟨t,ht⟩
      let N := Submodule.span R {t}
      have hN : ⊥ < N := by
        by_contra hc
        simp only [not_bot_lt_iff] at hc
        rw [Submodule.span_singleton_eq_bot.mp hc] at ht
        simp only [LinearMap.toSpanSingleton_zero, LinearMap.ker_zero] at ht
        exact Ideal.IsPrime.ne_top (ht ▸ hJ).1 rfl
      have h:= h N hN
      rw [prop3d12 ⟨(⊥, N), hN⟩] at h
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj] at h
      rw [← h] at hc
      have : (_μ R M ⟨(⊥, N), hN⟩) = {⟨J,hJ.1⟩} := by
        unfold _μ
        simp only
        ext s
        constructor
        · intro hs
          simp only [Set.mem_setOf_eq] at hs
          simp only [Set.mem_singleton_iff]
          rcases hs with ⟨p,⟨hp1,hp2⟩⟩
          have : p = J := by
            unfold associatedPrimes IsAssociatedPrime at hp1
            simp only [Set.mem_setOf_eq] at hp1
            have hp1 := hp1.2
            rcases hp1 with ⟨s,hs⟩
            rw [hs, ht]
            apply Eq.symm
            refine Submodule.ext ?_
            intro g
            constructor
            · intro hg
              simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
              let s' : M:= N.subtype s.out
              have hs' : s' ∈ N := by
                unfold s'
                simp only [Submodule.subtype_apply, SetLike.coe_mem]
              rcases (@Submodule.mem_span_singleton R M _ _ _ s' t).1 hs' with ⟨r₀,hr₀⟩
              have hfinal : g • s' = 0 := by
                rw [← hr₀,← smul_assoc]
                nth_rw 1 [smul_eq_mul]
                rw [CommRing.mul_comm,← smul_eq_mul,smul_assoc,hg]
                exact MulActionWithZero.smul_zero r₀
              unfold s' at hfinal
              simp only [Submodule.subtype_apply] at hfinal
              have hfinal' : (g • ↑(Quotient.out s) : M) = ↑(g • Quotient.out s) := by
                exact rfl
              have hfinal : g • Quotient.out s = 0 := Submodule.coe_eq_zero.mp <| hfinal' ▸ hfinal
              have : (⟦g • Quotient.out s⟧ : ↥N ⧸ Submodule.submoduleOf ⊥ N) = g • (Submodule.Quotient.mk (Quotient.out s)) := by rfl
              rw [hfinal] at this
              unfold Submodule.Quotient.mk Quotient.mk'' at this
              rw [Quotient.out_eq] at this
              exact this ▸ rfl
            · intro hg
              simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
              let s' : M:= N.subtype s.out
              have s'_ne0 : s' ≠ 0 := by
                by_contra hc
                unfold s' at hc
                simp only [Submodule.subtype_apply, ZeroMemClass.coe_eq_zero] at hc
                have : s = 0 := by
                  have := hc ▸ Quotient.out_eq s
                  exact id (Eq.symm this)
                rw [this] at hs
                simp only [LinearMap.toSpanSingleton_zero, LinearMap.ker_zero] at hs
                exact (Ideal.IsPrime.ne_top hp1.1) hs
              have hs' : g • s' = 0 := by
                unfold s'
                simp only [Submodule.subtype_apply]
                rw [((by rfl) : g • (↑(Quotient.out s) : M) = ↑(g • Quotient.out s))]
                refine ZeroMemClass.coe_eq_zero.mpr ?_
                have : (⟦g • Quotient.out s⟧ : ↥N ⧸ Submodule.submoduleOf ⊥ N) = g • (Submodule.Quotient.mk (Quotient.out s)) := by
                  exact rfl
                unfold Submodule.Quotient.mk Quotient.mk'' at this
                rw [Quotient.out_eq, hg] at this
                have this' : (Submodule.Quotient.mk (g • Quotient.out s) : ↥N ⧸ Submodule.submoduleOf ⊥ N) = ⟦g • Quotient.out s⟧ := by rfl
                exact Submodule.coe_eq_zero.mp <| (Submodule.Quotient.mk_eq_zero _).1 <| this' ▸ this
              have hst : s' ∈ Submodule.span R {t} := by
                unfold s'
                simp only [Submodule.subtype_apply, SetLike.coe_mem]
              rcases (@Submodule.mem_span_singleton R M _ _ _ s' t).1 hst with ⟨r₀,hr₀⟩
              rw [← hr₀,← smul_assoc] at hs'
              have : (g • r₀) ∈ J := by
                rw [ht]
                simp only [smul_eq_mul, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
                rw [← smul_eq_mul,hs']
              rw [smul_eq_mul] at this
              cases' hJ.1.mul_mem_iff_mem_or_mem.1 this with this this
              · rw [ht] at this
                simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
                exact this
              · rw [ht] at this
                simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
                rw [hr₀] at this
                exact False.elim <| s'_ne0 this
          simp only [← hp2, this]
        · intro hs
          simp only [Set.mem_singleton_iff] at hs
          simp only [Set.mem_setOf_eq]
          use s.asIdeal
          simp only [hs, exists_prop, and_true]
          unfold associatedPrimes IsAssociatedPrime
          simp only [Set.mem_setOf_eq]
          refine ⟨IsAssociatedPrime.isPrime hJ,?_⟩
          use Submodule.Quotient.mk ⟨t,Submodule.mem_span_singleton_self t⟩
          rw [ht]
          refine Submodule.ext ?_
          intro g
          constructor
          · intro hg
            simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
            have : ((g • Submodule.Quotient.mk (⟨t, Submodule.mem_span_singleton_self t⟩: ↥N)):↥N ⧸ Submodule.submoduleOf ⊥ N) = Submodule.Quotient.mk (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) := by
              exact rfl
            rw [this]
            simp only [SetLike.mk_smul_mk, Submodule.Quotient.mk_eq_zero]
            exact hg
          · intro hg
            simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
            have : ((g • Submodule.Quotient.mk (⟨t, Submodule.mem_span_singleton_self t⟩: ↥N)):↥N ⧸ Submodule.submoduleOf ⊥ N) = Submodule.Quotient.mk (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) := by
              exact rfl
            rw [hg] at this
            have this' : (g • ⟨t, Submodule.mem_span_singleton_self t⟩ : ↥N) = ( ⟨g • t,  Submodule.smul_mem N g <| Submodule.mem_span_singleton_self t⟩ : ↥N) := rfl
            simp only [this'] at this
            exact (Submodule.Quotient.mk_eq_zero _).1 this.symm
      simp only [this, Set.toFinset_singleton, Finset.min'_singleton, not_true_eq_false] at hc
  · intro h N hN
    have := prop3d12 (⟨(⊥, N), hN⟩)
    rw [this]
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
    have := assinc hN le_top
    have : (_μ R M ⟨(⊥, N), hN⟩).toFinset.min' (μ_nonempty ⟨(⊥, N), hN⟩) ∈ _μ R M ⟨(⊥, ⊤), bot_lt_top⟩ := by
      refine this ?_
      simp only [Set.mem_setOf_eq]
      have := (_μ R M ⟨(⊥, N), hN⟩).toFinset.min'_mem (μ_nonempty ⟨(⊥, N), hN⟩)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨t1,_⟩
      use t1
    simp only [Set.mem_setOf_eq] at this
    rcases this with ⟨p,⟨hp1,hp2⟩⟩
    have hp1 : p ∈ associatedPrimes R M := by
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _ (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
      exact LinearEquiv.trans t1 Submodule.topEquiv
    have hp1' : ((_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min' (μ_nonempty ⟨(⊥, ⊤), bot_lt_top⟩)).asIdeal ∈ associatedPrimes R M := by
      have := (_μ R M ⟨(⊥, ⊤), bot_lt_top⟩).toFinset.min'_mem (μ_nonempty ⟨(⊥, ⊤), bot_lt_top⟩)
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
      rcases this with ⟨p,⟨hp1,hp2⟩⟩
      rw [← hp2]
      convert hp1
      refine LinearEquiv.AssociatedPrimes.eq <| LinearEquiv.symm ?_
      have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _ (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
        (of_eq_true (Eq.trans (congrArg (fun x ↦ x = ⊥) (Submodule.ker_subtype ⊤)) (eq_self ⊥)))
        )
      exact LinearEquiv.trans t1 Submodule.topEquiv
    rw [← hp2]
    simp only [h.unique hp1 hp1']
    unfold _μ
    rfl

instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μ_Admissible (μ R M) where
  μ_adm := Or.inl inferInstance

open Classical



def lift_quot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : Submodule R M)
(x : Submodule R (N₂⧸(N₁.submoduleOf N₂))) : Submodule R M :=
  Submodule.map N₂.subtype (Submodule.comap (N₁.submoduleOf N₂).mkQ x)

lemma lift_quot_middle {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
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

lemma lift_quot_not_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(N₁ N₂ : Submodule R M)
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

lemma quot_ntl {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] {N₁ N₂ : ℒ R M} (hN : N₁ < N₂) : Nontrivial (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  apply Submodule.Quotient.nontrivial_of_lt_top
  apply lt_top_iff_ne_top.2
  by_contra hc
  have h' : ∀ x ∈ N₂, x ∈ N₁ := by
    intro x hx
    have : ⟨x,hx⟩ ∈ Submodule.submoduleOf N₁ N₂ := hc ▸ Submodule.mem_top
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at this
    exact this
  exact (not_lt_of_le h') <| hN

lemma quot_ntl' {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] {N₁ N₂ : ℒ R M} (hN : N₁ < N₂) : Nontrivial (@ℒ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _) :=
(Submodule.nontrivial_iff R).mpr <| (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)



lemma test {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
(N : Submodule R M) (N' : Submodule R ↥N)
(x : M) (hx1 : x ∈ N) (hx2 : x ∈ Submodule.map N.subtype N')
: ⟨x,hx1⟩ ∈ N' := by
  simp only [Submodule.mem_map, Submodule.subtype_apply, Subtype.exists, exists_and_right,
    exists_eq_right] at hx2
  rcases hx2 with ⟨a,b⟩
  exact b

set_option synthInstance.maxHeartbeats 0

lemma ss_iff' {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (N₁ N₂ : ℒ R M) (hN : N₁ < N₂) : Semistable (Resμ ⟨(N₁, N₂), hN⟩ (μ R M)) ↔ @Semistable (@ℒ R _ _ (↥N₂ ⧸ N₁.submoduleOf N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN)  _ _ _) (@quot_ntl' R _ _ M _ _ _ _ N₁ N₂ hN) _ _ (S R) _
(@μ R _ _ (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) (@quot_ntl R _ _ M _ _ _ _ N₁ N₂ hN) _ _ _) := by
  refine ⟨fun h ↦ ?_,fun h ↦ ?_⟩
  · have h := h.semistable
    have : Nontrivial (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) := quot_ntl hN
    have : Nontrivial (ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := quot_ntl' hN
    refine {semistable := ?_ }
    intro W hW
    have h := h ⟨(lift_quot N₁ N₂ W),(lift_quot_middle N₁ N₂  <| le_of_lt hN) W ⟩ (fun hc ↦ lift_quot_not_bot N₁ N₂ W hW (Subtype.coe_inj.mpr hc))
    convert h
    · rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, W), bot_lt_iff_ne_bot.mpr hW⟩ = _μ R M ⟨(↑(⊥ : Interval ⟨(N₁, N₂), hN⟩), lift_quot N₁ N₂ W), by
        refine lt_of_le_of_ne ?_ ?_
        · apply (lift_quot_middle _ _ _ _).1
          exact le_of_lt hN
        · apply Ne.symm
          exact lift_quot_not_bot N₁ N₂ W hW
        ⟩ := by
        unfold _μ
        simp only [ne_eq]
        ext x
        constructor
        · intro hx
          simp only [ne_eq, gt_iff_lt, not_lt, Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have wp : N₂.subtype (W.subtype q.out).out ∈ lift_quot N₁ N₂ W := by
            unfold lift_quot
            simp only [Submodule.subtype_apply, Submodule.mem_map, Submodule.mem_comap,
              Submodule.mkQ_apply, SetLike.coe_eq_coe, exists_eq_right]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
            apply SetLike.coe_mem
          use ((N₁).submoduleOf (lift_quot N₁ N₂ W)).mkQ ⟨N₂.subtype (W.subtype q.out).out,wp⟩
          simp only [Submodule.subtype_apply, Submodule.mkQ_apply]
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          constructor
          · intro hz
            have : z • (↑(Quotient.out (↑(Quotient.out q) : ↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) : M) ∈ N₁ := by
              have : z • Quotient.out (Quotient.out q).val ∈ N₁.submoduleOf N₂ := by
                have : z • Quotient.out (Quotient.out q).val - Quotient.out (z • Quotient.out q).val ∈ Submodule.submoduleOf N₁ N₂ := by
                  apply (Submodule.Quotient.mk_eq_zero _).1
                  simp only [SetLike.val_smul, Submodule.Quotient.mk_sub,
                    Submodule.Quotient.mk_smul]
                  unfold Submodule.Quotient.mk Quotient.mk''
                  simp only [Quotient.out_eq, sub_self]
                have this' : Quotient.out (z • Quotient.out q).val ∈ Submodule.submoduleOf N₁ N₂ := by
                  have : z • q.out = 0 := by
                    rw [← Quotient.out_eq (z • q)] at hz
                    apply (Submodule.Quotient.mk_eq_zero _).1 at hz
                    have : Submodule.submoduleOf ⊥ W = ⊥ := by
                      unfold Submodule.submoduleOf
                      simp only [Submodule.comap_bot, Submodule.ker_subtype]
                    simp only [this, Submodule.mem_bot] at hz
                    rw [← hz]
                    have : z • q.out - (z • q).out ∈ (⊥: Submodule R ↥W) := by
                      rw [← this]
                      apply (Submodule.Quotient.mk_eq_zero _).1
                      simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
                      unfold Submodule.Quotient.mk Quotient.mk''
                      simp only [Quotient.out_eq, sub_self]
                    simp only [Submodule.mem_bot] at this
                    exact sub_eq_zero.1 this
                  rw [this]
                  simp only [ZeroMemClass.coe_zero]
                  apply (Submodule.Quotient.mk_eq_zero _).1
                  unfold Submodule.Quotient.mk Quotient.mk''
                  apply Quotient.out_eq
                exact (Submodule.sub_mem_iff_left (Submodule.submoduleOf N₁ N₂) this').mp this
              exact this
            exact this
          · intro hz
            have hz : z • (Quotient.out (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ := hz
            have : z • Quotient.out (Quotient.out q).val - Quotient.out (z • (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ := by
              apply (Submodule.Quotient.mk_eq_zero _).1
              simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
              unfold Submodule.Quotient.mk Quotient.mk''
              simp only [Quotient.out_eq]
              apply sub_self
            have hz : Quotient.out (z • (Quotient.out q).val) ∈ Submodule.submoduleOf N₁ N₂ := by
              exact (Submodule.sub_mem_iff_right (Submodule.submoduleOf N₁ N₂) hz).mp this
            have hz : z • (Quotient.out q).val = 0 := by
              apply (Submodule.Quotient.mk_eq_zero _).2 at hz
              unfold Submodule.Quotient.mk Quotient.mk'' at hz
              simp only [Quotient.out_eq] at hz
              exact hz
            have hz : z • q.out = 0 := Submodule.coe_eq_zero.mp hz
            apply_fun (Submodule.submoduleOf ⊥ W).mkQ at hz
            simp only [map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at hz
            unfold Submodule.Quotient.mk Quotient.mk'' at hz
            simp only [Quotient.out_eq] at hz
            exact hz
        · intro hx
          simp only [ne_eq, gt_iff_lt, not_lt, Submodule.nontrivial_iff, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : q.out.val ∈ N₂ := by
            have : lift_quot N₁ N₂ W ≤ N₂ := Submodule.map_subtype_le N₂ (Submodule.comap (Submodule.submoduleOf N₁ N₂).mkQ W)
            exact this q.out.prop
          have this' : (N₁.submoduleOf N₂).mkQ ⟨q.out.val,this⟩ ∈ W := by
            exact test N₂ ((Submodule.comap (Submodule.submoduleOf N₁ N₂).mkQ W)) q.out.val this q.out.prop
          use ((⊥ : Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf W).mkQ (⟨(N₁.submoduleOf N₂).mkQ ⟨q.out.val,this⟩,this'⟩ : W)
          simp only [Submodule.mkQ_apply]
          have beb : Submodule.submoduleOf ⊥ W = ⊥ := by
              unfold Submodule.submoduleOf
              simp only [Submodule.comap_bot, Submodule.ker_subtype]
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, beb]
          simp only [SetLike.mk_smul_mk, Submodule.mem_bot, Submodule.mk_eq_zero]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          constructor
          · intro hz
            have : z • q.out ∈ (N₁.submoduleOf (lift_quot N₁ N₂ W)) := by
              apply (Submodule.Quotient.mk_eq_zero _).1
              simp only [Submodule.Quotient.mk_smul]
              unfold Submodule.Quotient.mk Quotient.mk''
              rw [Quotient.out_eq]
              exact hz
            exact this
          · intro hz
            simp only [SetLike.mk_smul_mk] at hz
            have hz : z • q.out ∈ N₁.submoduleOf (lift_quot N₁ N₂ W) := hz
            apply (Submodule.Quotient.mk_eq_zero _).2 at hz
            rw [Submodule.Quotient.mk_smul] at hz
            unfold Submodule.Quotient.mk Quotient.mk'' at hz
            simpa [Quotient.out_eq] using hz
      simp only [this]
    · rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, ⊤), bot_lt_top⟩ = _μ R M ⟨(N₁, N₂), hN⟩ := by
        unfold _μ
        simp only [ne_eq]
        ext x
        constructor
        · intro hx
          simp only [ne_eq, gt_iff_lt, not_lt, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          use q.out.val
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
          constructor
          · intro hz
            have : z • q.out.val = (z • q.out).val := rfl
            rw [this]
            have : z • q.out = 0 := by
              have: ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤).mkQ (z • Quotient.out q) = z • q := by
                simp only [map_smul, Submodule.mkQ_apply]
                unfold Submodule.Quotient.mk Quotient.mk''
                rw [Quotient.out_eq]
              rw [hz] at this
              apply (Submodule.Quotient.mk_eq_zero _).1 at this
              have this' : ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤) = ⊥ := by
                unfold Submodule.submoduleOf
                simp only [Submodule.comap_bot, Submodule.ker_subtype]
              simp only [this'] at this
              exact this
            rw [this]
            rfl
          · intro hz
            have hz : z • q.out = 0 := Submodule.coe_eq_zero.mp hz
            have: ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤).mkQ (z • Quotient.out q) = z • q := by
              simp only [map_smul, Submodule.mkQ_apply]
              unfold Submodule.Quotient.mk Quotient.mk''
              rw [Quotient.out_eq]
            rw [hz] at this
            simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_zero] at this
            exact this.symm
        · intro hx
          simp only [ne_eq, gt_iff_lt, not_lt, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : (N₁.submoduleOf N₂).mkQ q.out ∈ (⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := by
            simp only [Submodule.mkQ_apply, Submodule.mem_top]
          use Submodule.Quotient.mk (⟨(N₁.submoduleOf N₂).mkQ q.out, this⟩ : ↥(⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)))
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at *
          rw [← Submodule.Quotient.mk_smul]
          rw [Submodule.Quotient.mk_eq_zero]
          have this' : ((⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤) = ⊥ := by
            unfold Submodule.submoduleOf
            simp only [Submodule.comap_bot, Submodule.ker_subtype]
          rw [this']
          simp only [Submodule.mkQ_apply, SetLike.mk_smul_mk, Submodule.mem_bot,
            Submodule.mk_eq_zero]
          rw [← Submodule.Quotient.mk_smul]
          simp only [Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk Quotient.mk''
          simp only [Quotient.out_eq]
      simp only [this]
      rfl
  · have h := h.semistable
    have := quot_ntl hN; have := quot_ntl' hN
    refine {semistable := ?_ }
    intro W hW
    simp only [gt_iff_lt, not_lt] at *
    have : (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)) ≠ ⊥ := by
      by_contra hc
      refine hW ?_
      have : Submodule.comap N₂.subtype ↑W = N₁.submoduleOf N₂ := by
        ext x
        constructor
        · intro hx
          have : (N₁.submoduleOf N₂).mkQ x ∈ Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype ↑W) := by
            exact Submodule.mem_map_of_mem hx
          rw [hc] at this
          simpa only [Submodule.mkQ_apply, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] using this
        · intro hx
          exact W.prop.1 hx
      apply Subtype.coe_inj.1
      ext y
      constructor
      · intro hy
        have this' : (⟨y, W.prop.2 hy⟩ : N₂) ∈ Submodule.comap N₂.subtype ↑W := hy
        rw [this] at this'
        exact this'
      · intro hy
        exact W.prop.1 hy
    have h := h (Submodule.map (N₁.submoduleOf N₂).mkQ (Submodule.comap N₂.subtype W)) this
    convert h
    · rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R M ⟨(↑(⊥: Interval ⟨(N₁, N₂), hN⟩), ↑W), by
        simp only [Subtype.coe_lt_coe, bot_lt_iff_ne_bot, ne_eq, hW, not_false_eq_true]
      ⟩ = _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)
          ⟨(⊥, Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W)),
            Ne.bot_lt' (id (Ne.symm this))⟩ := by
        unfold _μ
        simp only [ne_eq]
        ext x
        constructor
        · intro hx
          simp only [Submodule.nontrivial_iff, ne_eq, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : (⟨q.out,W.prop.2 q.out.prop⟩ : N₂) ∈ (Submodule.comap (Submodule.subtype N₂) ↑W) := by
            simp only [Submodule.mem_comap, Submodule.subtype_apply, SetLike.coe_mem]
          have this' : (Submodule.submoduleOf N₁ N₂).mkQ (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩ : (Submodule.comap (Submodule.subtype N₂) ↑W)).val ∈ Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W) := by
            simp only [Submodule.mem_map]
            use (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩ : (Submodule.comap (Submodule.subtype N₂) ↑W))
          use Submodule.Quotient.mk ⟨(Submodule.submoduleOf N₁ N₂).mkQ (⟨(⟨q.out,W.prop.2 q.out.prop⟩ : N₂), this⟩ : (Submodule.comap (Submodule.subtype N₂) ↑W)).val,this'⟩
          simp only [Submodule.mkQ_apply]
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot,Submodule.mk_eq_zero,← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk, Submodule.mem_comap, Submodule.subtype_apply]
          have : z • q.out.val ∈ N₁ ↔ z • q.out ∈ (N₁.submoduleOf W.val) := { mp := fun h ↦ h, mpr := fun h ↦ h }
          rw [this, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
        · intro hx
          simp only [Submodule.nontrivial_iff, ne_eq, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : q.out.val.out ∈ W.val.submoduleOf N₂ := by
            refine Submodule.mem_comap.mpr ?_
            obtain ⟨x, hx₁, hx₂⟩ := Submodule.mem_map.mp q.out.property
            rw [Submodule.mem_comap] at hx₁
            show (Quotient.out q.out.val).val ∈ W.val
            obtain ⟨y, hy⟩ := QuotientAddGroup.mk_out_eq_mul (N₁.submoduleOf N₂).toAddSubgroup x
            change Quotient.out ((N₁.submoduleOf N₂).mkQ x) = x + y.val at hy
            rw [← hx₂, hy]
            show x.val + y.val.val ∈ W.val
            exact Submodule.add_mem _ hx₁ <| W.prop.1 y.property
          use Submodule.Quotient.mk (⟨q.out.val.out,this⟩ : W.val)
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          have : z • ⟨q.out.val.out.val, this⟩ ∈ Submodule.submoduleOf N₁ W.val ↔ z • q.out.val.out ∈ N₁.submoduleOf N₂ := Eq.to_iff rfl
          unfold Bot.bot OrderBot.toBot BoundedOrder.toOrderBot instBoundedOrderInterval
          rw [this, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
          unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
          have : z • q.out = 0 ↔ z • q.out.val = 0 := beq_eq_beq.mp rfl
          rw [← this]
          have : (z • q).out ∈ (⊥: Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W)) ↔ z • q = 0 := by
            rw [← Submodule.Quotient.mk_eq_zero]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
          rw [← this]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot]
          have : (z • q).out - z • q.out ∈ (⊥: ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf (Submodule.map (Submodule.submoduleOf N₁ N₂).mkQ (Submodule.comap (Submodule.subtype N₂) ↑W)) := by
            rw [← Submodule.Quotient.mk_eq_zero]
            simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq, Quotient.out_eq]
            exact sub_self (z • q)
          unfold Submodule.submoduleOf at this
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot] at this
          constructor
          · intro h
            rw [h] at this
            simpa only [zero_sub, neg_eq_zero] using this
          · intro h
            rw [h] at this
            simpa only [sub_zero] using this
      simp only [this]
    · rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, μA_res_intvl]
      rw [prop3d12]
      simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
        EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
      have : _μ R M ⟨(↑(⊥:Interval ⟨(N₁, N₂), hN⟩), ↑(⊤:Interval ⟨(N₁, N₂), hN⟩)), hN⟩ = _μ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂) ⟨(⊥, ⊤), bot_lt_top⟩ := by
        unfold _μ
        simp only [ne_eq]
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hx
          simp only [Submodule.nontrivial_iff, ne_eq, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          have : q ∈ (⊤ : ℒ R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)) := trivial
          use Submodule.Quotient.mk ⟨q,this⟩
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          simp only [SetLike.mk_smul_mk]
          unfold Submodule.submoduleOf
          simp only [Submodule.comap_bot, Submodule.ker_subtype, Submodule.mem_bot, Submodule.mk_eq_zero]
        · intro hx
          simp only [Submodule.nontrivial_iff, ne_eq, Set.mem_setOf_eq] at *
          rcases hx with ⟨p,⟨hp1,hp2⟩⟩
          use p
          rw [← hp2]
          simp only [exists_prop, and_true]
          unfold associatedPrimes at *
          simp only [Set.mem_setOf_eq] at *
          simp only [Set.mem_setOf_eq] at hp1
          unfold IsAssociatedPrime at *
          refine ⟨hp1.1,?_⟩
          rcases hp1.2 with ⟨q,hq1,hq2⟩
          use Submodule.Quotient.mk q.out.val.out
          ext z
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          unfold Submodule.Quotient.mk Quotient.mk''
          rw [Quotient.out_eq]
          have : z • q.out.val = (z • q.out).val := rfl
          rw [this]
          have : (z • q.out).val = 0 ↔ z • q.out = 0 := Submodule.coe_eq_zero
          rw [this]
          have :  z • q = 0 ↔ (z • q).out ∈ Submodule.submoduleOf ⊥ ⊤ := by
            rw [← Submodule.Quotient.mk_eq_zero]
            unfold Submodule.Quotient.mk Quotient.mk''
            rw [Quotient.out_eq]
          rw [this]
          have : (⊥ :  Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤ = ⊥ := by
            unfold Submodule.submoduleOf
            simp only [Submodule.comap_bot, Submodule.ker_subtype]
          simp only [this, Submodule.mem_bot]
          have this' : (z • q).out - z • q.out ∈ (⊥ :  Submodule R (↥N₂ ⧸ Submodule.submoduleOf N₁ N₂)).submoduleOf ⊤ := by
            apply (Submodule.Quotient.mk_eq_zero _).1
            simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
            unfold Submodule.Quotient.mk Quotient.mk''
            simp only [Quotient.out_eq, sub_self]
          simp only [this, Submodule.mem_bot] at this'
          constructor
          · intro h
            rw [h] at this'
            simpa only [zero_sub, neg_eq_zero] using this'
          · intro h
            rw [h] at this'
            simpa only [sub_zero] using this'
      simp only [this]


lemma piecewise_coprimary {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (HNFil : HarderNarasimhanFiltration (μ R M)):
∀ n < Nat.find HNFil.fin_len, Coprimary R (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) := by
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
  have ttt : Semistable (μ R (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)))) := by
    rw [← ss_iff']
    exact this
  exact { coprimary := rmk4d14₂.mp ttt }


noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Inhabited (CoprimaryFiltration R M) := by
  have HNFil := (inferInstance : Inhabited (HarderNarasimhanFiltration (μ R M))).default
  refine { default := { filtration := HNFil.filtration, monotone := HNFil.monotone, first_eq_bot := HNFil.first_eq_bot, fin_len := HNFil.fin_len, strict_mono := HNFil.strict_mono, piecewise_coprimary := fun n hn ↦ piecewise_coprimary HNFil n hn, strict_mono_associated_prime := ?_ } }
  intro n hn
  have := lt_of_not_le <| HNFil.μA_pseudo_strict_anti n hn
  repeat rw [prop3d12] at this
  simp only [Int.reduceNeg, Int.rawCast.eq_1, Int.cast_eq, Nat.rawCast.eq_1, Int.cast_ofNat_Int,
    Int.reduceAdd, Int.ofNat_eq_coe, Nat.cast_ofNat, Nat.cast_id, Int.natCast_add, eq_mp_eq_cast,
    id_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.lt_iff_lt] at this
  apply S₀_order'.2 at this
  have pcn := (piecewise_coprimary HNFil n <| Nat.lt_of_succ_lt hn).coprimary
  have pcnp1 := (piecewise_coprimary HNFil (n+1) hn).coprimary
  have t' : (_μ R M ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)), HNFil.strict_mono (n+1) (n+2) (Nat.lt_add_one (n + 1)) hn⟩).toFinset.min' (μ_nonempty
      ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)),
        HNFil.strict_mono (n + 1) (n + 2) (Nat.lt_add_one (n + 1)) hn⟩) = {asIdeal := pcnp1.exists.choose, isPrime := pcnp1.exists.choose_spec.out.1} := by
    have := ((_μ R M ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)), HNFil.strict_mono (n+1) (n+2) (Nat.lt_add_one (n + 1)) hn⟩).toFinset.min'_mem (μ_nonempty
      ⟨(HNFil.filtration (n + 1), HNFil.filtration (n + 2)),
        HNFil.strict_mono (n + 1) (n + 2) (Nat.lt_add_one (n + 1)) hn⟩)).out
    apply Set.mem_toFinset.mp at this
    rcases this.out with ⟨p,hp1,hp2⟩
    rw [← hp2]
    simp only [pcnp1.unique pcnp1.exists.choose_spec hp1]
  have t'' : (_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1) (Nat.lt_add_one n) (Nat.le_of_succ_le hn)⟩).toFinset.min' (μ_nonempty ⟨(HNFil.filtration n, HNFil.filtration (n + 1)),
        HNFil.strict_mono n (n + 1) (Nat.lt_add_one n) (Nat.le_of_succ_le hn)⟩) = {asIdeal := pcn.exists.choose, isPrime := pcn.exists.choose_spec.out.1} := by
    have := ((_μ R M ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n+1) (Nat.lt_add_one n) <| le_of_lt hn⟩).toFinset.min'_mem (μ_nonempty
      ⟨(HNFil.filtration n, HNFil.filtration (n + 1)),
        HNFil.strict_mono n (n + 1) (Nat.lt_add_one n) <| le_of_lt hn⟩)).out
    apply Set.mem_toFinset.mp at this
    rcases this.out with ⟨p,hp1,hp2⟩
    rw [← hp2]
    simp only [pcn.unique pcn.exists.choose_spec hp1]
  exact t' ▸ t'' ▸ this

instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Nonempty (CoprimaryFiltration R M) := inferInstance

lemma CP_HN {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (a : CoprimaryFiltration R M) : ∃ HNFil : HarderNarasimhanFiltration (μ R M), a.filtration = HNFil.filtration := by
  let ahn : HarderNarasimhanFiltration (μ R M) := by
      refine { filtration := a.filtration, monotone := a.monotone, first_eq_bot := a.first_eq_bot, piecewise_semistable := ?_, fin_len := a.fin_len, strict_mono := a.strict_mono, μA_pseudo_strict_anti := ?_ }
      · intro i hi
        have := a.piecewise_coprimary i hi
        have ntl : Nontrivial (↥(a.filtration (i + 1)) ⧸ Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1))) := by
          apply Submodule.Quotient.nontrivial_of_lt_top
          apply lt_top_iff_ne_top.2
          by_contra hc
          have h' : ∀ x ∈ a.filtration (i + 1), x ∈ a.filtration i := by
            intro x hx
            have : ⟨x,hx⟩ ∈ Submodule.submoduleOf (a.filtration i) (a.filtration (i + 1)) := hc ▸ Submodule.mem_top
            simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at this
            exact this
          exact (not_lt_of_le h') <| a.strict_mono i (i+1) (lt_add_one i) hi
        have this := this.coprimary
        rw [← rmk4d14₂,← ss_iff'] at this
        exact this
      · intro i hi
        have := a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)
        repeat rw [prop3d12]
        simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Int.reduceNeg,
          Int.rawCast.eq_1, Int.cast_eq, Nat.rawCast.eq_1, Int.cast_ofNat_Int, Int.reduceAdd,
          Int.ofNat_eq_coe, Nat.cast_ofNat, Nat.cast_id, Int.natCast_add, eq_mp_eq_cast, id_eq,
          OrderEmbedding.le_iff_le, not_le, gt_iff_lt]
        apply S₀_order'.1
        have := a.strict_mono_associated_prime i hi
        convert this
        · have := (_μ R M ⟨(a.filtration (i + 1), a.filtration (i + 2)), a.strict_mono (i+1) (i+2) (Nat.lt_add_one (i + 1)) hi⟩).toFinset.min'_mem (μ_nonempty ⟨(a.filtration (i + 1), a.filtration (i + 2)), a.strict_mono (i+1) (i+2) (Nat.lt_add_one (i + 1)) hi⟩)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          simp only [(a.piecewise_coprimary (i+1) hi).coprimary.unique ((a.piecewise_coprimary (i+1) hi).coprimary.exists.choose_spec) hp1]
        · have := (_μ R M ⟨(a.filtration i, a.filtration (i + 1)), a.strict_mono i (i+1) (Nat.lt_add_one i) (Nat.le_of_succ_le hi)⟩).toFinset.min'_mem (μ_nonempty ⟨(a.filtration i, a.filtration (i + 1)), a.strict_mono i (i+1) (Nat.lt_add_one i) (Nat.le_of_succ_le hi)⟩)
          apply Set.mem_toFinset.mp at this
          rcases this.out with ⟨p,hp1,hp2⟩
          rw [← hp2]
          simp only [(a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.unique ((a.piecewise_coprimary i (Nat.lt_of_succ_lt hi)).coprimary.exists.choose_spec) hp1]
  use ahn

lemma CP_HN' {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ CPFil : CoprimaryFiltration R M, CPFil.filtration = (inferInstance : Inhabited (HarderNarasimhanFiltration (μ R M))).default.filtration := by
  intro CPFil
  rcases (CP_HN CPFil) with ⟨HNFil, hfil⟩
  have := @instUniqueHarderNarasimhanFiltration (ℒ R M) _ _ _ _ (S R) inferInstance (μ R M) (@prop3d13₂ R _ _ M _ _ _ _) _
  rw [hfil,this.uniq HNFil, this.uniq (@default (HarderNarasimhanFiltration (μ R M)) inferInstance)]

noncomputable instance {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Unique (CoprimaryFiltration R M) where
  uniq := by
    intro a
    have t2 := CP_HN' (@default (CoprimaryFiltration R M) instInhabitedCoprimaryFiltration)
    rw [← CP_HN' a] at t2
    ext
    rw [t2]

end impl

end HarderNarasimhan
