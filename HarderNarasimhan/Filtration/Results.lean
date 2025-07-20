import HarderNarasimhan.Filtration.Defs
import HarderNarasimhan.Filtration.Impl

noncomputable instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
Inhabited (HardarNarasimhanFiltration μ) := by
  refine { default :=
    { filtration := impl.HNFil μ,
      first_eq_bot := by simp [impl.HNFil],
      fin_len := impl.of_fin_len μ,
      strict_mono := ?_,
      piecewise_semistable := ?_,
      μA_not_increaing := ?_ } }
  sorry
  sorry
  sorry

noncomputable instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
Nonempty (HardarNarasimhanFiltration μ) := inferInstance
