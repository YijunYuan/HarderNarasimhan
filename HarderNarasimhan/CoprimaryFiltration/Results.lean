import HarderNarasimhan.CoprimaryFiltration.Impl

namespace HarderNarasimhan

lemma μ_nonempty {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M]  [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2}, (_μ R M I).toFinset.Nonempty
------------
:= impl.μ_nonempty

lemma μmax_eq_μ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2},
  μmax (μ R M) I = (μ R M) I
------------
:= impl.noname

instance proposition_3_11 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Convex (μ R M)
------------
:= by
  apply (impl.Convex_iff _).1
  infer_instance


lemma proposition_3_12 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
∀ I : {z: (ℒ R M) × (ℒ R M) // z.1 < z.2},
  μA (μ R M) I = ({(((_μ R M) I).toFinset.min' (μ_nonempty I))} : S₀ R)
------------
:= impl.prop3d12

lemma proposition_3_13 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
WellFoundedGT (ℒ R M) ∧
μA_DescendingChainCondition (μ R M)
------------
:= ⟨inferInstance,inferInstance⟩

lemma remark_3_14 {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
List.TFAE [
Semistable (μ R M),
∀ N : (ℒ R M), (hN : ⊥ < N) →
  μA (μ R M) ⟨(⊥,N),hN⟩ = ({(((_μ R M) ⟨(⊥,⊤),bot_lt_top⟩).toFinset.min' (μ_nonempty ⟨(⊥,⊤),bot_lt_top⟩))} : S₀ R),
∃! p, p ∈ associatedPrimes R M
]
------------
:= by
  tfae_have 1 ↔ 2 := impl.rmk4d14₁
  tfae_have 1 ↔ 3 := impl.rmk4d14₂
  tfae_finish

instance theorem_3_15₁ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Nonempty (CoprimaryFiltration R M)
------------
:= inferInstance

noncomputable
instance theorem_3_15₂ {R : Type*} [CommRing R] [IsNoetherianRing R]
{M : Type*} [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M] :
------------
Unique (CoprimaryFiltration R M)
------------
:= inferInstance

end HarderNarasimhan
