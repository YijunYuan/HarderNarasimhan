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

lemma S₀_order' {R : Type} [CommRing R] [IsNoetherianRing R] {a b : LinearExtension (PrimeSpectrum R)}:  a < b ↔ ({a} : (S₀ R)) < ({b} : (S₀ R)) := by
  refine le_iff_le_iff_lt_iff_lt.mp ?_
  simp only [S₀_order.2]

abbrev S (R : Type) [CommRing R] [IsNoetherianRing R] := @DedekindMacNeilleCompletion (S₀ R) instPartialOrderS₀

abbrev ℒ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:= Submodule R M

abbrev _μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
(I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}) : Set (LinearExtension (PrimeSpectrum R)) :=
{ {asIdeal := p, isPrime := h.out.1} | (p : Ideal R) (h : p ∈ associatedPrimes R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) }

noncomputable instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]
{I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}} : Fintype ((_μ R M) I) := (Set.Finite.dependent_image (associatedPrimes.finite R (I.val.2⧸(Submodule.submoduleOf I.val.1 I.val.2))) (fun I hI ↦ ({asIdeal := I, isPrime := hI.out.1} : LinearExtension (PrimeSpectrum R)))).fintype

noncomputable abbrev μ (R : Type) [CommRing R] [IsNoetherianRing R]
(M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]:
{z: (ℒ R M) × (ℒ R M) // z.1 < z.2} → (S R) := fun I ↦ coe'.toFun ((_μ R M) I).toFinset

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


instance prop_3_11 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Convex (μ R M) := by
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

lemma prop_3_12 {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : ∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, μA (μ R M) I = ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R) := by
  intro I
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
  unfold μA

  sorry

instance prop_3_13₁ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : WellFoundedGT (ℒ R M) := wellFoundedGT

instance prop_3_13₂ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μA_DescendingChainCondition (μ R M) where
  μ_dcc := by
    intro N x hx1 hx2
    by_contra hc
    simp at hc
    simp only [prop_3_12, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      OrderEmbedding.le_iff_le, not_le] at hc
    have hc := fun w ↦ S₀_order'.mpr (hc w)
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

lemma rmk4d14₁ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∀ N : (ℒ R M), (hN : ⊥ < N) → μA (μ R M) ⟨(⊥,N),hN⟩ = ({(((_μ R M) ⟨(⊥,⊤),bot_lt_top⟩).toFinset.min' (μ_nonempty ⟨(⊥,⊤),bot_lt_top⟩))} : S₀ R) := by
  constructor
  · intro hst
    intro N hN
    have hst := hst.semistable N (bot_lt_iff_ne_bot.1 hN)
    simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding]
    rw [prop_3_12 ⟨(⊥,N),hN⟩, prop_3_12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩] at hst
    rw [prop_3_12 ⟨(⊥,N),hN⟩]
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
    have t1 := prop_3_12 ⟨(⊥,N),bot_lt_iff_ne_bot.2 hN⟩
    have t2 := prop_3_12 ⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩
    rw [t1] at h
    simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj] at h
    rw [t1,t2]
    simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, gt_iff_lt,
      OrderEmbedding.lt_iff_lt, not_lt, ge_iff_le]
    apply (S₀_order.2 _ _).1
    rw [h]

class Coprimary (R : Type) [CommRing R] [IsNoetherianRing R](M : Type) [AddCommGroup M] [Module R M] : Prop where
  coprimary : ∀ x : R, (∃ m : M, m ≠ 0 ∧ x • m = 0) → ∃ n : Nat, n > 0 ∧ x^n ∈ Module.annihilator R M

theorem Coprimary_iff  {R : Type} [CommRing R] [IsNoetherianRing R] {M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Coprimary R M ↔ ∃! p, p ∈ associatedPrimes R M := sorry


set_option maxHeartbeats 0
lemma rmk4d14₂ {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : Semistable (μ R M) ↔ ∃! p, p ∈ associatedPrimes R M := by
  rw [rmk4d14₁]
  constructor
  · intro h
    have := prop_3_12 (⟨((⊥ : ℒ R M), ⊤), bot_lt_top⟩)
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
      have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _ (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
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
        have t1 := @Submodule.quotEquivOfEqBot R ↥(⊤ : Submodule R M) _ _ _ (Submodule.submoduleOf (⊥: Submodule R M) (⊤: Submodule R M)) (id
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
      rw [prop_3_12 ⟨(⊥, N), hN⟩] at h
      simp at h
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
                simp at hc
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
    have := prop_3_12 (⟨(⊥, N), hN⟩)
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

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] : μ_Admissible (μ R M) where
  μ_adm := by
    right
    intro I
    unfold IsAttained


    sorry

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

lemma ss_iff {R : Type} [CommRing R] [IsNoetherianRing R] {M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] (HNFil : HardarNarasimhanFiltration (μ R M)) (n : ℕ) (hn : n < Nat.find HNFil.fin_len) (
ntl : Nontrivial (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1)))) :
Semistable (Resμ ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n + 1) (lt_add_one n) hn⟩ (μ R M)) ↔ Semistable (μ R (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))))  := by
  constructor
  intro this
  refine {semistable := ?_}
  intro x hx
  have := this.semistable ⟨lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x, lift_quot_middle (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone <| Nat.le_succ n) x⟩ <| (by
    apply Subtype.coe_ne_coe.1
    simp only [ne_eq]
    exact lift_quot_not_bot (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone <| Nat.le_succ n) x hx
  )
  convert this
  · have htool : HNFil.filtration n < lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x := by
      sorry
    have : μA (Resμ ⟨(HNFil.filtration n, HNFil.filtration (n + 1)), HNFil.strict_mono n (n + 1) (lt_add_one n) hn⟩ (μ R M)) ⟨(⊥, ⟨lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x, lift_quot_middle (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone (Nat.le_succ n)) x⟩), bot_lt_iff_ne_bot.mpr (Subtype.coe_ne_coe.mp (id (lift_quot_not_bot (HNFil.filtration n) (HNFil.filtration (n + 1)) (HNFil.monotone (Nat.le_succ n)) x hx)))⟩ = μA (μ R M) ⟨(HNFil.filtration n,lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x),htool⟩ := by
      unfold μA
      congr
      ext t
      constructor
      · intro ht
        simp at *
        rcases ht with ⟨a,ha1,ha2⟩
        use a.val
        use ⟨ha1.1,fun hc ↦ ha1.right (Subtype.coe_inj.mp hc)⟩
        rw [← ha2]
        unfold μmax
        congr
        ext z
        constructor
        · intro hz
          simp at *
          rcases hz with ⟨p,hp1,hp2⟩
          use ⟨p,le_trans a.prop.1 hp1.1.1,sorry⟩
          rw [← hp2]


          sorry
        · sorry
      · sorry
    rw [this]
    repeat rw [prop_3_12]
    simp only [ne_eq, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
      EmbeddingLike.apply_eq_iff_eq, Finset.singleton_inj]
    have : _μ R (↥(HNFil.filtration (n + 1)) ⧸ Submodule.submoduleOf (HNFil.filtration n) (HNFil.filtration (n + 1))) ⟨(⊥, x), bot_lt_iff_ne_bot.mpr hx⟩ =  _μ R M ⟨(HNFil.filtration n, lift_quot (HNFil.filtration n) (HNFil.filtration (n + 1)) x), htool⟩ := by
      unfold _μ
      simp

      sorry
    simp only [this]
  ·
    sorry
  sorry


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
  refine Coprimary_iff.2 <| rmk4d14₂.1 <| ?_
  rw [← ss_iff]
  exact this
  exact hn

instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Nonempty (CoprimaryFiltration R M) := inferInstance

noncomputable instance {R : Type} [CommRing R] [IsNoetherianRing R]
{M : Type} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
Unique (CoprimaryFiltration R M) where
  uniq := by
    intro a
    let ahn : HardarNarasimhanFiltration (μ R M) := by
      refine { filtration := a.filtration, monotone := a.monotone, first_eq_bot := a.first_eq_bot, piecewise_semistable := ?_, fin_len := a.fin_len, strict_mono := a.strict_mono, μA_pseudo_strict_anti := ?_ }
      ·
        sorry
      · intro i hi
        have := a.coprimary i (Nat.lt_of_succ_lt hi)




        sorry
    sorry


end HardarNarasimhan
