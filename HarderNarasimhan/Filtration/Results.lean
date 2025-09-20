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
      exact fun i j hij ↦ if h : i = j then (by rw [h]) else (if h' : j ≤ impl.HNlen μ then (le_of_lt <| impl.HNFil_is_strict_mono' μ i j (lt_of_le_of_ne hij h) h') else ((this) j <| le_of_lt <| lt_of_not_ge h') ▸ le_top)
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
    rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
    exact fun a ↦ HarderNarasimhanFiltration.ext (funext fun n ↦ congrFun (impl.theorem3d10 μ hμ hμcvx a.filtration a.first_eq_bot a.fin_len a.strict_mono (Nat.le_induction (Nat.find_spec a.fin_len) fun n _ hn' ↦ eq_top_iff.2 <| hn' ▸ a.monotone (Nat.le_succ n)) a.piecewise_semistable fun i  ↦ by
    have : ∀ (j : ℕ) (hij : i + 1 ≤ j) (hj : j < Nat.find a.fin_len),
  μA μ ⟨(HarderNarasimhanFiltration.filtration a i, HarderNarasimhanFiltration.filtration a (i + 1)), HarderNarasimhanFiltration.strict_mono a i (i + 1) (lt_add_one i)
  (by linarith)⟩ >
    μA μ ⟨(HarderNarasimhanFiltration.filtration a j, HarderNarasimhanFiltration.filtration a (j + 1)), HarderNarasimhanFiltration.strict_mono a j (j + 1) (lt_add_one j)
  hj⟩ := by
      apply Nat.le_induction
      · exact fun hj ↦ lt_of_not_ge (a.μA_pseudo_strict_anti i hj)
      · refine fun j hij hind hj ↦ gt_trans (hind (Nat.lt_of_succ_lt hj)) ?_
        exact lt_of_not_ge <| a.μA_pseudo_strict_anti j hj
    exact fun j hij hj ↦ this j hij hj
  ) n)

open Fin.NatCast
theorem exists_relSeries_isIntervalSemistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ] [h : μ_Admissible μ] :
------------
∃ s : RelSeries (IsIntervalSemistable μ),
  s.head = ⊥ ∧ s.last = ⊤ ∧
  ∀ i : ℕ, (hi : i + 1 < s.length) →
    ¬   μA μ ⟨(s.toFun i, s.toFun ↑(i+1)), by simp [*]⟩
      ≤ μA μ ⟨(s.toFun ↑(i+1), s.toFun ↑(i+2)), by simp [*]⟩
------------
 := by
  let HNfil : HarderNarasimhanFiltration μ := default
  let HNseq : RelSeries (IsIntervalSemistable μ) := {
    toFun := fun n ↦ HNfil.filtration n,
    length := Nat.find HNfil.fin_len
    step := by
      intro i
      use HNfil.strict_mono i.val (i.succ).val (Nat.lt_add_one i.val) <| Fin.is_le i.succ
      exact HNfil.piecewise_semistable i.val i.prop
  }
  use HNseq
  refine ⟨rfl,Nat.find_spec HNfil.fin_len,?_⟩
  refine fun i hi hc ↦ HNfil.μA_pseudo_strict_anti i hi ?_
  convert hc
  · refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans (Nat.lt_add_one i) <| lt_trans hi (Nat.lt_add_one _)
  · refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans hi (Nat.lt_add_one _)
  · refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans hi (Nat.lt_add_one _)
  · refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact Nat.succ_lt_succ hi



theorem exists_unique_relSeries_isIntervalSemistable_of_completeLinearOrder {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]:
------------
∃! s : RelSeries (IsIntervalSemistable μ),
  s.head = ⊥ ∧ s.last = ⊤ ∧
  ∀ i : ℕ, (hi : i + 1 < s.length) →
    ¬   μA μ ⟨(s.toFun i, s.toFun ↑(i+1)), by simp [*]⟩
      ≤ μA μ ⟨(s.toFun ↑(i+1), s.toFun ↑(i+2)), by simp [*]⟩
------------
:= by
  apply existsUnique_of_exists_of_unique
  · exact exists_relSeries_isIntervalSemistable μ
  · intro F1 F2 h1 h2
    rcases impl.hHFil_of_hNSeries μ F1 h1 with ⟨HN1,len1⟩
    rcases impl.hHFil_of_hNSeries μ F2 h2 with ⟨HN2,len2⟩
    have t1 := instUniqueHarderNarasimhanFiltration.uniq HN1
    have t2 := instUniqueHarderNarasimhanFiltration.uniq HN2
    have := t2.symm ▸ t1
    have len_eq : F1.length = F2.length := by
      rw [← len1.2, ← len2.2, this]
    ext x
    · rw [← len1.2, ← len2.2, this]
    · simp only [Function.comp_apply]
      have := congrFun (congrArg HarderNarasimhanFiltration.filtration this) ↑x
      rw [len1.1,len2.1] at this
      convert this
      · simp only [Fin.cast_val_eq_self]
        if hx : ↑x ≤ F1.length then
          simp only [hx, ↓reduceIte]
        else
          simp only [hx, ↓reduceIte]
          simp only [not_le] at hx
          have := Fin.is_le x
          exfalso
          linarith
      · simp only [Fin.cast_val_eq_self]
        if hx : ↑x ≤ F2.length then
          simp only [hx, ↓reduceIte]
          congr
          refine Fin.eq_of_val_eq ?_
          refine Eq.symm (Fin.val_cast_of_lt ?_)
          exact Nat.lt_add_one_of_le hx
        else
          simp only [hx, ↓reduceIte]
          simp only [not_le] at hx
          have : ↑x ≤ F2.length := len_eq ▸ Fin.is_le x
          exfalso
          linarith


end HarderNarasimhan
