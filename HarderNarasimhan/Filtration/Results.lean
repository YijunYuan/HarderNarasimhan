import HarderNarasimhan.Filtration.Defs
import HarderNarasimhan.Filtration.Impl


open Classical


noncomputable instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
Inhabited (HardarNarasimhanFiltration μ) := by
  refine { default :=
    { filtration := impl.HNFil μ,
      first_eq_bot := by simp [impl.HNFil],
      fin_len := impl.HNFil_of_fin_len μ,
      strict_mono := impl.HNFil_is_strict_mono' μ,
      piecewise_semistable := impl.HNFil_piecewise_semistable μ,
      μA_not_increaing := impl.HNFil_μA_not_increaing μ,
      monotone := by
        intro i j hij
        by_cases h : i = j
        · rw [h]
        · by_cases h' : j ≤ impl.HNlen μ
          · exact le_of_lt <| impl.HNFil_is_strict_mono' μ i j (lt_of_le_of_ne hij h) h'
          · have : ∀ n : ℕ, impl.HNlen μ ≤ n → impl.HNFil μ n = ⊤ := by
              apply Nat.le_induction
              · exact Nat.find_spec (impl.HNFil_of_fin_len μ)
              · intro n hn hn'
                simp only [impl.HNFil,hn']
                simp
            exact (this j <| le_of_lt <| lt_of_not_le h') ▸ le_top
         } }


noncomputable instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
Nonempty (HardarNarasimhanFiltration μ) := inferInstance


noncomputable instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] :
Unique (HardarNarasimhanFiltration μ) where
  uniq := by
    intro a
    ext n
    exact congrFun (impl.theorem3d10 μ hμ hμcvx a.filtration a.first_eq_bot a.fin_len a.strict_mono (Nat.le_induction (Nat.find_spec a.fin_len) fun n hn hn' ↦ eq_top_iff.2 <| hn' ▸ a.monotone (Nat.le_succ n)) a.piecewise_semistable fun i j hij hj ↦ lt_of_not_ge <| a.μA_not_increaing i j hij hj) n
