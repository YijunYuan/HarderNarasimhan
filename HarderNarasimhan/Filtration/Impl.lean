import HarderNarasimhan.Filtration.Defs

namespace HarderNarasimhan

namespace impl

open Classical in
noncomputable def HNFil {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ]
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNFil μ n
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨(prev_term , ⊤) , lt_top_iff_ne_top.2 htop⟩ : {p : ℒ × ℒ // p.1 < p.2})
      (impl.prop3d8₁' μ hμ I' (Convex_of_Convex_large TotIntvl I' ⟨bot_le,le_top⟩ μ hμcvx)
      (Or.casesOn h.μ_adm (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨(I'.val.1 , z) ,  lt_of_le_of_ne hzI.left hz⟩)).choose


lemma HNFil_prop_of_def {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ n : Nat, (h' : HNFil μ n ≠ ⊤) →
IsGreatest (StI μ ⟨(HNFil μ n , ⊤), lt_top_iff_ne_top.2 h'⟩) (HNFil μ (n + 1)) := by
  intro n h'
  simp only [HNFil, h']
  exact (HNFil._proof_4 μ n h').choose_spec


lemma HNFil_is_strict_mono {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ n : Nat, HNFil μ n ≠ ⊤ → HNFil μ n < HNFil μ (n + 1) := fun
    n hn ↦ lt_of_le_of_ne (HNFil_prop_of_def μ n hn).1.1.1 (HNFil_prop_of_def μ n hn).1.2.1


lemma HNFil_of_fin_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[inst_3 : WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ]
: ∃ N : Nat, HNFil μ N = ⊤ := by
  by_contra!
  exact (wellFounded_iff_isEmpty_descending_chain.1 inst_3.wf).elim
    ⟨fun n => HNFil μ n, fun n => HNFil_is_strict_mono μ n (this n)⟩

open Classical in
noncomputable def HNlen {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] : Nat := Nat.find (HNFil_of_fin_len μ)

open Classical in
lemma HNFil_ne_top_iff_lt_len {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
  ∀ n : Nat, HNFil μ n ≠ ⊤ ↔ n < HNlen μ := by
  intro n
  constructor
  · intro hn
    by_contra!
    have h : ∀ n : ℕ, (hn' : HNlen μ ≤ n) → HNFil μ n = ⊤ := by
      apply Nat.le_induction
      · exact Nat.find_spec (HNFil_of_fin_len μ)
      · intro k hk hk'
        simp only [HNFil, hk', ↓reduceDIte]
    exact hn (h n this)
  · exact fun hn ↦ Nat.find_min (HNFil_of_fin_len μ) hn


lemma HNFil_is_strict_mono' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ]
[h : μ_Admissible μ] :
∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := by
  intro i
  have h' : ∀ j : ℕ, i + 1 ≤ j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := Nat.le_induction
    (fun hi ↦
      HNFil_is_strict_mono μ i
        ((HNFil_ne_top_iff_lt_len μ i).2 (Nat.add_one_le_iff.1 hi)))
    fun k _ hk' hk'' ↦
    lt_trans (hk' (le_trans (Nat.le_succ k) hk''))
      (HNFil_is_strict_mono μ k
        ((HNFil_ne_top_iff_lt_len μ k).2 (Nat.add_one_le_iff.1 hk'')))
  exact fun j hj hij ↦ h' j (Nat.add_one_le_iff.2 hj) hij

open Classical in
lemma HNFil_piecewise_semistable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ] [h : μ_Admissible μ] :
∀ i : ℕ, (h: i < Nat.find (HNFil_of_fin_len μ)) →
    Semistable (Resμ ⟨(HNFil μ i, HNFil μ (i+1)),
      HNFil_is_strict_mono' μ i (i+1) (lt_add_one i) h⟩ μ) :=
  fun i hi ↦ (semistableI_iff μ ⟨(HNFil μ i , HNFil μ (i+1)),
    HNFil_is_strict_mono' μ i (i+1) (lt_add_one i) hi⟩).1 <|
    impl.prop3d7₁ μ ⟨(HNFil μ i , ⊤), lt_top_iff_ne_top.2 <|
    Nat.find_min (HNFil_of_fin_len μ) hi⟩ (HNFil μ (i + 1))
    (HNFil_prop_of_def μ i (Nat.find_min (HNFil_of_fin_len μ) hi)).1

open Classical in
lemma HNFil_μA_pseudo_strict_anti {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
[WellFoundedGT ℒ] {S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
[hμ : μA_DescendingChainCondition μ] [hμcvx : ConvexI TotIntvl μ] [h : μ_Admissible μ] :
∀ i : ℕ, (hi : i + 1 < Nat.find (HNFil_of_fin_len μ)) →
  ¬ μA μ ⟨(HNFil μ i, HNFil μ (i+1)),
      HNFil_is_strict_mono μ i (Nat.find_min (HNFil_of_fin_len μ) (Nat.lt_of_succ_lt hi))⟩ ≤
    μA μ ⟨(HNFil μ (i+1), HNFil μ (i+2)),
      HNFil_is_strict_mono μ (i + 1) (Nat.find_min (HNFil_of_fin_len μ) hi)⟩ := by
  intro i hj
  refine impl.prop3d7₂ μ ⟨(HNFil μ i,⊤),lt_top_iff_ne_top.2 <| Nat.find_min (HNFil_of_fin_len μ) <|
    lt_trans (lt_add_one i) hj⟩ (Convex_of_Convex_large TotIntvl ⟨(HNFil μ i,⊤),lt_top_iff_ne_top.2
    <| Nat.find_min (HNFil_of_fin_len μ) <| lt_trans (lt_add_one i) hj⟩ ⟨bot_le,le_top⟩ μ hμcvx)
    (HNFil μ (i + 1)) (HNFil_prop_of_def μ i <| Nat.find_min (HNFil_of_fin_len μ) <| lt_trans
    (lt_add_one i) hj).1 (HNFil μ (i + 1 + 1)) (?_) ?_
  exact ⟨le_of_lt <| lt_trans (HNFil_is_strict_mono μ i <| Nat.find_min (HNFil_of_fin_len μ) <|
    lt_trans (lt_add_one i) hj) <| HNFil_is_strict_mono μ (i + 1) <|
    Nat.find_min (HNFil_of_fin_len μ) <| hj,le_top⟩

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} : μ_Admissible μ :=
{μ_adm := Or.inl Std.instTotalLeOfIsLinearPreorder}

open Classical in
theorem theorem3d10 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : ConvexI TotIntvl μ)
(f : ℕ → ℒ) (hf0 : f 0 = ⊥)
(hffin : ∃ n : ℕ, f n = ⊤)
(hfsi : ∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ Nat.find hffin → f i < f j)
(ffst : ∀ i : ℕ, i ≥ Nat.find hffin → f i = ⊤)
(hss : ∀ j : ℕ, (hj : j < Nat.find hffin) →
  Semistable (Resμ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩ μ))
(hmua: ∀ i : ℕ, ∀ j : ℕ, (hij : i < j) → (hj : j < Nat.find hffin) →
  μA μ ⟨(f i, f (i+1)), hfsi i (i+1) (lt_add_one i) <| (by omega)⟩ >
  μA μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) <| hj⟩)
: f = HNFil μ := by
  have hss := fun j hj ↦ (semistableI_iff μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩).2
    <| hss j hj
  let HNFilt := HNFil μ
  funext k
  induction k with
  | zero => simp only [hf0, HNFil]
  | succ n hn =>
  · by_cases h₁ : n + 1 ≤ Nat.find hffin
    · have h₂ : ∃ N : ℕ, N ≥ (n+1) ∧ HNFilt (n+1) ≤ f N :=
        ⟨Nat.find hffin, h₁, by simp only [ge_iff_le, le_refl, ffst, le_top]⟩
      let i : ℕ := Nat.find h₂
      have h₃ := (HNFil_is_strict_mono μ n <| Nat.find_min (HNFil_of_fin_len μ) <|
        lt_of_lt_of_le (lt_add_one n) <| Nat.add_one_le_iff.2 ((HNFil_ne_top_iff_lt_len μ n).mp
        (Eq.rec (motive := fun x h ↦ n < Nat.find hffin → ¬x = ⊤)
        (Nat.find_min hffin) hn (lt_of_lt_of_le (lt_add_one n) h₁))))
      have h₁₅ : i ≥ n + 1 := (Nat.find_spec h₂).1
      have h₄ : ¬ HNFilt (n+1) ≤ f (i-1) := by
        have h₅ := Nat.find_min h₂ (Nat.sub_one_lt <| ne_of_gt
          <| lt_of_lt_of_le (Nat.add_one_pos n) h₁₅ )
        apply not_and_or.1 at h₅
        rcases h₅ with h₅ | h₅
        · simp only [ge_iff_le, not_le] at h₅
          nth_rw 1 [← hn,
                    ← eq_of_le_of_ge (Nat.le_of_lt_add_one h₅) (Nat.sub_le_sub_right h₁₅ 1)] at h₃
          exact not_le_of_gt h₃
        · exact h₅
      have h₁₃ : HNFilt n ≤ f (i - 1) := by
        simp only [HNFilt]
        rw [← hn]
        have h₁₄ : n ≤ i - 1 := Nat.le_sub_one_of_lt h₁₅
        rw [le_iff_eq_or_lt] at h₁₄
        rcases h₁₄ with h₁₄ | h₁₄
        · rw [h₁₄]
        · apply le_of_lt
          have : i ≤ Nat.find hffin := by
            by_contra!
            rcases not_and_or.1 <| Nat.find_min h₂ this with c₁ | c₂
            · exact c₁ h₁
            · simp only [Nat.find_spec hffin, le_top, not_true_eq_false] at c₂
          exact hfsi n (i-1) h₁₄ (by omega)
      have h₆ := impl.lem2d4₃I TotIntvl μ hμcvx (HNFilt (n + 1)) (in_TotIntvl (HNFilt (n + 1)))
        (f (i - 1)) (in_TotIntvl (f (i - 1))) h₄ (HNFilt n) <| le_inf (le_of_lt h₃) h₁₃
      have h₉ : i > 0 := Nat.zero_lt_of_lt h₁₅
      have h₈ : i - 1 < Nat.find hffin := by
        apply Nat.sub_one_lt_of_le h₉
        by_contra!
        rcases not_and_or.1 <| Nat.find_min h₂ this with c₁ | c₂
        · exact c₁ h₁
        · simp only [Nat.find_spec hffin, le_top, not_true_eq_false] at c₂
      have h₇ : f (i-1) < f i := (congrArg (fun _a ↦ f (i - 1) < f _a) (Nat.sub_add_cancel h₉)) ▸
        (hfsi (i - 1) i (Nat.sub_one_lt_of_lt h₁₅) (Nat.le_of_pred_lt h₈))
      have h₁₀ : μA μ ⟨(HNFilt n, HNFilt (n+1)), h₃⟩ ≤ μA μ ⟨(f (i-1),f i), h₇⟩ := by
        have h₁₁ := hss (i-1) h₈
        simp only [Nat.sub_one_add_one <| ne_of_gt h₉] at h₁₁
        exact le_trans h₆ <| le_of_not_gt (h₁₁.out.choose_spec.2.1 (HNFilt (n + 1) ⊔ f (i - 1))
          ⟨le_sup_right,sup_le_iff.2 ⟨(Nat.find_spec h₂).2,le_of_lt h₇⟩⟩
          <| ne_of_lt <|right_lt_sup.2 h₄)
      have h₁₂ : i = n + 1 := by
        refine eq_of_le_of_not_lt' h₁₅ ?_
        by_contra!
        have : HNFilt n < f (n+1):= by
          simp only [HNFilt, ← hn]
          apply hfsi n (n+1) (lt_add_one n) h₁
        have h₁₂ : μA μ ⟨(HNFilt n, HNFilt (n + 1)), h₃⟩ < μA μ ⟨(HNFilt n, f (n+1)),this⟩ := by
          have h₁₃ := hmua n (i-1) (by (expose_names; exact Nat.lt_sub_of_add_lt this_1)) h₈
          simp only [hn, Nat.sub_one_add_one <| ne_of_gt h₉, gt_iff_lt] at h₁₃
          exact lt_of_le_of_lt h₁₀ h₁₃
        exact ((HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le this le_top
          ).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt this,le_top⟩ <| ne_of_lt this) h₁₂
      have h₁₄ := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg f h₁₂)
      have h₁₉ : HNFilt n < f (n+1) := by
          simp only [HNFilt]
          rw [← hn, ← h₁₂]
          nth_rw 1 [h₁₂] at h₇
          exact h₇
      have h₁₆ : f n < HNFilt (n + 1):= Eq.mpr (hn ▸ rfl)
        (HNFil_is_strict_mono μ n (ne_of_lt (lt_of_lt_of_le h₃ le_top)))
      have h₁₇ := le_of_not_gt <| (hss n h₁).out.choose_spec.choose_spec.1
        (HNFilt (n+1)) ⟨le_of_lt h₁₆,h₁₄⟩ <| ne_of_lt h₁₆
      simp only [hn] at h₁₇
      exact eq_of_le_of_ge ((HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top
        ).1.out.choose_spec.choose_spec.2 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ (ne_of_lt h₁₉)
        (eq_of_le_of_not_lt h₁₇ <| (HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top
        ).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ <| ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [ffst (n+1) (Nat.le_of_succ_le h₁),eq_comm]
      rw [ffst n (Nat.le_of_lt_succ h₁)] at hn
      exact not_ne_iff.1 <| (HNFil_ne_top_iff_lt_len μ (n+1)).not.2 (not_lt_of_ge <| le_of_lt <|
        Nat.lt_add_one_iff.2 <| le_of_not_gt <| (HNFil_ne_top_iff_lt_len μ n).not.1
        (not_ne_iff.2 hn.symm))

section Fil_to_RelSeries
open Fin.NatCast
@[simp]
lemma balabala1 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
(s : RelSeries (IntervalSemistableRel μ))
{i : ℕ} (hi : i + 1 < s.length)
 : s.toFun ↑i < s.toFun ↑(i + 1) := by
  have := (s.step ⟨i,Nat.lt_of_succ_lt hi⟩).choose
  simp only [Fin.castSucc_mk, Fin.succ_mk] at this
  convert this
  · exact Fin.val_cast_of_lt <| lt_trans (Nat.lt_add_one _) <| lt_trans hi <| Nat.lt_add_one _
  · exact Fin.val_cast_of_lt <| lt_trans hi <| Nat.lt_add_one _

@[simp]
lemma balabala2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S}
(s : RelSeries (IntervalSemistableRel μ))
{i : ℕ} (hi : i + 1 < s.length)
 : s.toFun ↑(i + 1) < s.toFun ↑(i + 2) := by
  have := (s.step ⟨i+1, hi⟩).choose
  simp only [Fin.castSucc_mk, Fin.succ_mk] at this
  convert this
  · exact Fin.val_cast_of_lt <| Nat.lt_add_right 1 hi
  · simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
    exact Nat.succ_lt_succ hi

open Classical in
lemma hHFil_of_hNSeries {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(F1 : RelSeries (IntervalSemistableRel μ))
(h1 : F1.head = ⊥ ∧ F1.last = ⊤ ∧
  ∀ i : ℕ, (hi : i + 1 < F1.length) →
    ¬   μA μ ⟨(F1.toFun i, F1.toFun ↑(i+1)), balabala1 F1 hi⟩
      ≤ μA μ ⟨(F1.toFun ↑(i+1), F1.toFun ↑(i+2)), balabala2 F1 hi⟩) :
∃ HN1 : HarderNarasimhanFiltration μ,
  HN1.filtration = (fun n ↦ if n ≤ F1.length then F1.toFun n else ⊤) ∧
                   (Nat.find HN1.fin_len = F1.length) := by
  let filtration1 := fun n ↦ if n ≤ F1.length then F1.toFun n else ⊤
  have hstrange : ∃ n, (if n ≤ F1.length then F1.toFun ↑n else ⊤) = ⊤ := by
    use F1.length
    simp only [le_refl, Fin.natCast_eq_last]
    exact h1.2.1
  have Fmono : ∀ i j : ℕ, i < j → j ≤ F1.length → F1.toFun ↑i < F1.toFun ↑j := by
    intro i
    apply Nat.le_induction
    · intro h
      convert (F1.step ⟨i,h⟩).choose
      · refine Fin.eq_mk_iff_val_eq.mpr ?_
        refine Fin.val_cast_of_lt ?_
        exact Nat.lt_add_right 1 h
      · refine Fin.eq_mk_iff_val_eq.mpr ?_
        refine Fin.val_cast_of_lt ?_
        exact Nat.add_lt_add_right h 1
    · intro n hn hind h
      refine lt_trans (hind (Nat.le_of_succ_le h)) ?_
      have := (F1.step ⟨n , h⟩).choose
      simp only [Fin.castSucc_mk, Fin.succ_mk] at this
      convert this
      · refine Fin.val_cast_of_lt ?_
        exact Nat.lt_add_right 1 h
      · refine Fin.val_cast_of_lt ?_
        exact Nat.add_lt_add_right h 1
  have hslen : Nat.find hstrange  = F1.length := by
      have := Nat.find_min' hstrange ((by
        unfold filtration1
        simp only [le_refl, ↓reduceIte, Fin.natCast_eq_last]
        exact h1.2.1
        ) : filtration1 F1.length = ⊤)
      refine le_antisymm this ?_
      by_contra hc
      apply lt_of_not_ge at hc
      have t := Nat.find_spec hstrange
      simp only [if_pos this] at t
      have := t ▸ Fmono (Nat.find hstrange) F1.length hc le_rfl
      simp_all only [not_le, ite_eq_right_iff, Nat.find_le_iff, Nat.find_lt_iff,
        Fin.natCast_eq_last, not_top_lt]
  let HN1 : HarderNarasimhanFiltration μ := {
      filtration := filtration1,
      monotone := by
        refine monotone_nat_of_le_succ ?_
        intro n
        if hn : n ≤ F1.length then
          simp only [filtration1,hn, ↓reduceIte]
          if hn' : n + 1 ≤ F1.length then
            simp only [hn', ↓reduceIte]
            convert le_of_lt (F1.step ⟨n,hn'⟩).choose
            · simp only [Fin.castSucc_mk]
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.lt_add_right 1 hn'
            · simp only [Fin.succ_mk]
              refine Fin.eq_mk_iff_val_eq.mpr ?_
              refine Fin.val_cast_of_lt ?_
              exact Nat.add_lt_add_right hn' 1
          else
          simp only [hn', ↓reduceIte, le_top]
        else
        simp only [filtration1,hn, ↓reduceIte, top_le_iff, ite_eq_right_iff]
        intro hn'
        exfalso
        linarith,
      first_eq_bot := by
        simp only [filtration1,zero_le, ↓reduceIte]
        exact h1.1,
      fin_len := by
        use F1.length
        simp only [filtration1,le_refl, ↓reduceIte, Fin.natCast_eq_last]
        exact h1.2.1,
      strict_mono := by
        intro i j hij hj
        rw [hslen] at hj
        simp only [le_of_lt <| lt_of_lt_of_le hij hj, ↓reduceIte, hj, filtration1]
        exact Fmono i j hij hj,
      piecewise_semistable := by
        intro i hi
        unfold filtration1
        rw [hslen] at hi
        convert (F1.step ⟨i,hslen ▸ hi⟩).choose_spec
        · simp only [le_of_lt hi, ↓reduceIte, Fin.castSucc_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this': i + 1 ≤ F1.length := by linarith
          simp only [this', ↓reduceIte, Fin.succ_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.add_lt_add_right hi 1
        · simp only [le_of_lt hi, ↓reduceIte, Fin.castSucc_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp only [this', ↓reduceIte, Fin.succ_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.add_lt_add_right hi 1
        · simp only [le_of_lt hi, ↓reduceIte, Fin.castSucc_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp only [this', ↓reduceIte, Fin.succ_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.add_lt_add_right hi 1
        · simp only [le_of_lt hi, ↓reduceIte, Fin.castSucc_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.lt_add_right 1 hi
        · have this' : i + 1 ≤ F1.length := by linarith
          simp only [this', ↓reduceIte, Fin.succ_mk]
          congr
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          refine Fin.val_cast_of_lt ?_
          exact Nat.add_lt_add_right hi 1,
      μA_pseudo_strict_anti := by
        intro i hi
        have := h1.2.2 i (hslen ▸ hi)
        unfold filtration1
        rw [hslen] at hi
        convert this
        · have this' : i ≤ F1.length := by linarith
          simp only [this', ↓reduceIte]
        · simp only [le_of_lt hi, ↓reduceIte]
        · simp only [le_of_lt hi, ↓reduceIte]
        · have : i + 2 ≤ F1.length := hi
          simp only [this, ↓reduceIte]
    }
  use HN1

end Fil_to_RelSeries

end impl

end HarderNarasimhan
