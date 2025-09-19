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
    rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
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
  · simp only [Fin.val_natCast]
    refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans (Nat.lt_add_one i) <| lt_trans hi (Nat.lt_add_one _)
  · simp only [Fin.val_natCast]
    refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans hi (Nat.lt_add_one _)
  · simp only [Fin.val_natCast]
    refine Eq.symm (Nat.mod_eq_of_lt ?_)
    exact lt_trans hi (Nat.lt_add_one _)
  · simp only [Fin.val_natCast]
    refine Eq.symm (Nat.mod_eq_of_lt ?_)
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
    let filtration1 := fun n ↦ if n ≤ F1.length then F1.toFun n else ⊤
    have hstrange : ∃ n, (if n ≤ F1.length then F1.toFun ↑n else ⊤) = ⊤ := by
      use F1.length
      simp only [le_refl, Fin.natCast_eq_last]
      exact h1.2.1
    have hslen : Nat.find hstrange  = F1.length := by
      have := Nat.find_min' hstrange ((by
        unfold filtration1
        simp only [le_refl, ↓reduceIte, Fin.natCast_eq_last, filtration1]
        exact h1.2.1
        ) : filtration1 F1.length = ⊤)
      refine le_antisymm this ?_
      by_contra hc
      apply lt_of_not_le at hc
      have t := Nat.find_spec hstrange
      simp only [if_pos this] at t

      sorry
    let HN1 : HarderNarasimhanFiltration μ := {
      filtration := filtration1,
      monotone := by
        refine monotone_nat_of_le_succ ?_
        intro n
        if hn : n ≤ F1.length then
          simp only [filtration1,hn, ↓reduceIte]
          if hn' : n + 1 ≤ F1.length then
            simp only [hn', ↓reduceIte]
            have := le_of_lt (F1.step ⟨n,hn'⟩).choose
            convert this
            · simp only [Fin.castSucc_mk]
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.lt_add_right 1 hn'
            · simp
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.add_lt_add_right hn' 1
          else
          simp only [hn', ↓reduceIte, le_top]
        else
        simp only [filtration1,hn, ↓reduceIte, top_le_iff, ite_eq_right_iff]
        intro hn'
        exfalso
        linarith
        ,
      first_eq_bot := by
        simp only [filtration1,zero_le, ↓reduceIte]
        exact h1.1
        ,
      fin_len := by
        use F1.length
        simp only [filtration1,le_refl, ↓reduceIte, Fin.natCast_eq_last]
        exact h1.2.1
        ,
      strict_mono := by
        intro i j hij hj
        rw [hslen] at hj
        simp [hj,le_of_lt <| lt_of_lt_of_le hij hj,filtration1]
        sorry,
      piecewise_semistable := by
        intro i hi
        have := (F1.step ⟨i,hslen ▸ hi⟩).choose_spec
        unfold filtration1
        simp
        rw [hslen] at hi
        convert this
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this': i + 1 ≤ F1.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        ,
      μA_pseudo_strict_anti := by
        intro i hi
        have := h1.2.2 i (hslen ▸ hi)
        unfold filtration1
        rw [hslen] at hi
        convert this
        · have this' : i ≤ F1.length := by linarith
          simp [this']
        · simp [le_of_lt hi]
        · simp [le_of_lt hi]
        · have : i + 2 ≤ F1.length := by omega
          simp [this]
    }
    let filtration2 := fun n ↦ if n ≤ F2.length then F2.toFun n else ⊤
    have hstrange2 : ∃ n, (if n ≤ F2.length then F2.toFun ↑n else ⊤) = ⊤ := by
      use F2.length
      simp
      exact h2.2.1
    have hslen : Nat.find hstrange2  = F2.length := by
      have := Nat.find_min' hstrange2 ((by
        unfold filtration2
        simp only [le_refl, ↓reduceIte, Fin.natCast_eq_last, filtration2]
        exact h2.2.1
        ) : filtration2 F2.length = ⊤)
      refine le_antisymm this ?_
      by_contra hc
      apply lt_of_not_le at hc
      have t := Nat.find_spec hstrange
      simp only [if_pos this] at t

      sorry
    let HN2 : HarderNarasimhanFiltration μ := {
      filtration := filtration2,
      monotone := by
        refine monotone_nat_of_le_succ ?_
        intro n
        if hn : n ≤ F2.length then
          simp only [filtration2,hn, ↓reduceIte]
          if hn' : n + 1 ≤ F2.length then
            simp only [hn', ↓reduceIte]
            have := le_of_lt (F2.step ⟨n,hn'⟩).choose
            convert this
            · simp only [Fin.castSucc_mk]
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.lt_add_right 1 hn'
            · simp
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.add_lt_add_right hn' 1
          else
          simp only [hn', ↓reduceIte, le_top]
        else
        simp only [filtration2,hn, ↓reduceIte, top_le_iff, ite_eq_right_iff]
        intro hn'
        exfalso
        linarith
        ,
      first_eq_bot := by
        simp only [filtration2,zero_le, ↓reduceIte]
        exact h2.1
        ,
      fin_len := by
        use F2.length
        simp only [filtration2,le_refl, ↓reduceIte, Fin.natCast_eq_last]
        exact h2.2.1
        ,
      strict_mono := by
        intro i j hij hj
        rw [hslen] at hj
        simp [hj,le_of_lt <| lt_of_lt_of_le hij hj,filtration2]
        sorry,
      piecewise_semistable := by
        intro i hi
        have := (F2.step ⟨i,hslen ▸ hi⟩).choose_spec
        unfold filtration2
        simp
        rw [hslen] at hi
        convert this
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this': i + 1 ≤ F2.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F2.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F2.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        · simp [le_of_lt hi]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F2.length := by linarith
          simp [this']
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          linarith
        ,
      μA_pseudo_strict_anti := by
        intro i hi
        have := h2.2.2 i (hslen ▸ hi)
        unfold filtration2
        rw [hslen] at hi
        convert this
        · have this' : i ≤ F2.length := by linarith
          simp [this']
        · simp [le_of_lt hi]
        · simp [le_of_lt hi]
        · have : i + 2 ≤ F2.length := by omega
          simp [this]
    }
    have t1 := instUniqueHarderNarasimhanFiltration.uniq HN1
    have t2 := instUniqueHarderNarasimhanFiltration.uniq HN2
    have := t2.symm ▸ t1
    have len_eq : F1.length = F2.length := by
      expose_names
      rw [← hslen_1]
      have : Nat.find HN1.fin_len = Nat.find HN2.fin_len := by
        rw [this]
      rw [this,hslen]
    ext x
    · exact len_eq
    · simp only [Function.comp_apply]
      have : HN1.filtration x.val = HN2.filtration x.val := by
        rw [this]
      have : filtration1 x.val = filtration2 x.val := by
        exact this
      unfold filtration1 filtration2 at this
      simp only [Fin.is_le x, ↓reduceIte, Fin.cast_val_eq_self] at this
      have t' := Fin.is_le x
      simp only [len_eq] at t'
      simp only [t', ↓reduceIte] at this
      convert this
      refine Fin.eq_of_val_eq ?_
      simp only [Fin.coe_cast, Fin.val_natCast]
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_one_of_le t'


end HarderNarasimhan
