import HarderNarasimhan.Filtration.Defs
import HarderNarasimhan.Filtration.Impl


open Classical

namespace HarderNarasimhan

noncomputable instance instInhabitedHarderNarasimhanFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
------------
Inhabited (HarderNarasimhanFiltration μ) where
------------
default :=
  { filtration           := impl.HNFil μ,
    first_eq_bot         := of_eq_true (eq_self ⊥),
    fin_len              := impl.HNFil_of_fin_len μ,
    strict_mono          := impl.HNFil_is_strict_mono' μ,
    piecewise_semistable := impl.HNFil_piecewise_semistable μ,
    μA_pseudo_strict_anti:= impl.HNFil_μA_pseudo_strict_anti μ,
    monotone             := by
      have : ∀ n : ℕ, impl.HNlen μ ≤ n → impl.HNFil μ n = ⊤ := Nat.le_induction (Nat.find_spec (impl.HNFil_of_fin_len μ)) (fun n hn hn' ↦ (by simp only [impl.HNFil,hn']; simp))
      exact fun i j hij ↦ if h : i = j then (by rw [h]) else (if h' : j ≤ impl.HNlen μ then (le_of_lt <| impl.HNFil_is_strict_mono' μ i j (lt_of_le_of_ne hij h) h') else ((this) j <| le_of_lt <| lt_of_not_le h') ▸ le_top)
  }


instance instNonemptyHarderNarasimhanFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
------------
Nonempty (HarderNarasimhanFiltration μ)
------------
:= inferInstance


noncomputable instance instUniqueHarderNarasimhanFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] :
------------
Unique (HarderNarasimhanFiltration μ)
------------
where
  uniq := by
    rw [← impl.Convex_iff] at hμcvx
    exact fun a ↦ HarderNarasimhanFiltration.ext (funext fun n ↦ congrFun (impl.theorem3d10 μ hμ hμcvx a.filtration a.first_eq_bot a.fin_len a.strict_mono (Nat.le_induction (Nat.find_spec a.fin_len) fun n _ hn' ↦ eq_top_iff.2 <| hn' ▸ a.monotone (Nat.le_succ n)) a.piecewise_semistable fun i  ↦ by
    have : ∀ (j : ℕ) (hij : i + 1 ≤ j) (hj : j < Nat.find a.fin_len),
  μA μ ⟨(HarderNarasimhanFiltration.filtration a i, HarderNarasimhanFiltration.filtration a (i + 1)), HarderNarasimhanFiltration.strict_mono a i (i + 1) (lt_add_one i)
  (Decidable.byContradiction fun a_1 ↦
    impl.theorem3d10._proof_5 (HarderNarasimhanFiltration.filtration a) (HarderNarasimhanFiltration.fin_len a) i j hij hj
      a_1)⟩ >
    μA μ ⟨(HarderNarasimhanFiltration.filtration a j, HarderNarasimhanFiltration.filtration a (j + 1)), HarderNarasimhanFiltration.strict_mono a j (j + 1) (lt_add_one j)
  hj⟩ := by
      apply Nat.le_induction
      · exact fun hj ↦ lt_of_not_ge (a.μA_pseudo_strict_anti i hj)
      · refine fun j hij hind hj ↦ gt_trans (hind (Nat.lt_of_succ_lt hj)) ?_
        exact lt_of_not_ge <| a.μA_pseudo_strict_anti j hj
    exact fun j hij hj ↦ this j hij hj
  ) n)

end HarderNarasimhan
