import HarderNarasimhan.Filtration.Defs

namespace impl

open Classical

noncomputable def HNFil {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ]
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNFil μ n
    letI := Classical.propDecidable
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨(prev_term , ⊤) , lt_top_iff_ne_top.2 htop⟩ : {p : ℒ × ℒ // p.1 < p.2})
      (impl.prop3d8₁' μ hμ I' (Convex_of_Convex_large TotIntvl I' ⟨bot_le,le_top⟩ μ hμcvx) (Or.casesOn
       h.μ_adm (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨(I'.val.1 , z) ,  lt_of_le_of_ne hzI.left hz⟩)).choose


lemma HNFil_prop_of_def {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ] :
∀ n : Nat, (h' : HNFil μ n ≠ ⊤) → IsGreatest (StI μ ⟨(HNFil μ n , ⊤), lt_top_iff_ne_top.2 h'⟩) (HNFil μ (n + 1)) := by
  intro n h'
  simp only [HNFil, h']
  exact (HNFil._proof_4 μ n h').choose_spec


lemma is_strict_mono {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ] :
∀ n : Nat, HNFil μ n ≠ ⊤ → HNFil μ n < HNFil μ (n + 1) := fun
    n hn ↦ lt_of_le_of_ne (HNFil_prop_of_def μ n hn).1.1.1 (HNFil_prop_of_def μ n hn).1.2.1


lemma of_fin_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ]
: ∃ N : Nat, HNFil μ N = ⊤ := by
  by_contra!
  exact (WellFounded.wellFounded_iff_no_descending_seq.1 inst_3.wf).elim ⟨fun n => HNFil μ n, fun n => is_strict_mono μ n (this n)⟩


noncomputable def HNlen {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ] : Nat := by
  letI := Classical.propDecidable
  exact Nat.find (of_fin_len μ)


lemma ne_top_iff_lt_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ] :
  ∀ n : Nat, HNFil μ n ≠ ⊤ ↔ n < HNlen μ := by
  letI := Classical.propDecidable
  intro n
  constructor
  · intro hn
    by_contra!
    have h : ∀ n : ℕ, (hn' : HNlen μ ≤ n) → HNFil μ n = ⊤ := by
      apply Nat.le_induction
      · exact Nat.find_spec (of_fin_len μ)
      · intro k hk hk'
        simp [HNFil,hk']
    exact hn (h n this)
  · exact fun hn ↦ Nat.find_min (of_fin_len μ) hn


lemma is_strict_mono' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : μA_DescendingChainCondition μ] [hμcvx : Convex μ]
[h : μ_Admissible μ] :
∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := by
  intro i
  have h' : ∀ j : ℕ, i + 1 ≤ j → j ≤ HNlen μ → HNFil μ i < HNFil μ j := Nat.le_induction
    (fun hi ↦
      is_strict_mono μ i
        ((ne_top_iff_lt_len μ i).2 (Nat.add_one_le_iff.1 hi)))
    fun k _ hk' hk'' ↦
    lt_trans (hk' (le_trans (Nat.le_succ k) hk''))
      (is_strict_mono μ k
        ((ne_top_iff_lt_len μ k).2 (Nat.add_one_le_iff.1 hk'')))
  exact fun j hj hij ↦ h' j (Nat.add_one_le_iff.2 hj) hij

instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p :ℒ × ℒ // p.1 < p.2} → S} : μ_Admissible μ := {μ_adm := Or.inl <| LE.isTotal}


theorem theorem3d10  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(f : ℕ → ℒ) (hf0 : f 0 = ⊥)
(hffin : ∃ n : ℕ, f n = ⊤)
(hfsi : ∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ Nat.find hffin → f i < f j)
--(hfsi : ∀ i : ℕ, i < Nat.find hffin → f i < f (i + 1))
(ffst : ∀ i : ℕ, i ≥ Nat.find hffin → f i = ⊤)
(hss : ∀ j : ℕ, (hj : j < Nat.find hffin) → Semistable (Resμ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩ μ))
(hmua: ∀ i : ℕ, ∀ j : ℕ, (hij : i < j) → (hj : j + 1 ≤ Nat.find hffin) → μA μ ⟨(f i, f (i+1)), hfsi i (i+1) (lt_add_one i) <| (by omega)⟩ > μA μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) <| (by omega)⟩)
: f = HNFil μ := by
  have hss := fun j hj ↦ (semistableI_iff μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩).2 <| hss j hj
  let HNFilt := HNFil μ
  funext k
  induction' k with n hn
  · simp only [hf0, HNFil]
  · by_cases h₁ : n + 1 ≤ Nat.find hffin
    · have h₂ : ∃ N : ℕ, N ≥ (n+1) ∧ HNFilt (n+1) ≤ f N := ⟨Nat.find hffin, h₁, by simp [ffst]⟩
      let i : ℕ := Nat.find h₂
      have h₃ := (is_strict_mono μ n <| Nat.find_min (of_fin_len μ) <| lt_of_lt_of_le (lt_add_one n) <| Nat.add_one_le_iff.2 ((ne_top_iff_lt_len μ n).mp (Eq.rec (motive := fun x h ↦ n < Nat.find hffin → ¬x = ⊤) (Nat.find_min hffin) hn (lt_of_lt_of_le (lt_add_one n) h₁))))
      have h₁₅ : i ≥ n + 1 := (Nat.find_spec h₂).1
      have h₄ : ¬ HNFilt (n+1) ≤ f (i-1) := by
        have h₅ := Nat.find_min h₂ (Nat.sub_one_lt <| ne_of_gt <| lt_of_lt_of_le (Nat.add_one_pos n) h₁₅ )
        apply not_and_or.1 at h₅
        cases' h₅ with h₅ h₅
        · simp at h₅
          nth_rw 1 [← hn, ← eq_of_le_of_le (Nat.le_of_lt_add_one h₅) (Nat.sub_le_sub_right h₁₅ 1)] at h₃
          exact not_le_of_lt h₃
        · exact h₅
      have h₁₃ : HNFilt n ≤ f (i - 1) := by
        simp only [HNFilt]
        rw [← hn]
        have h₁₄ : n ≤ i - 1 := by omega
        rw [le_iff_eq_or_lt] at h₁₄
        cases' h₁₄ with h₁₄ h₁₄
        · rw [h₁₄]
        · apply le_of_lt
          have : i ≤ Nat.find hffin := by
            by_contra!
            cases' not_and_or.1 <| Nat.find_min h₂ this with c₁ c₂
            · exact c₁ h₁
            · simp [Nat.find_spec hffin] at c₂
          exact hfsi n (i-1) h₁₄ (by omega)
      have h₆ := impl.lem2d4₃I TotIntvl μ hμcvx (HNFilt (n + 1)) (in_TotIntvl (HNFilt (n + 1))) (f (i - 1)) (in_TotIntvl (f (i - 1))) h₄ (HNFilt n) <| le_inf (le_of_lt h₃) h₁₃
      have h₉ : i > 0 := by omega
      have h₈ : i - 1 < Nat.find hffin := by
        apply Nat.sub_one_lt_of_le h₉
        by_contra!
        cases' not_and_or.1 <| Nat.find_min h₂ this with c₁ c₂
        · exact c₁ h₁
        · simp [Nat.find_spec hffin] at c₂
      have h₇ : f (i-1) < f i := (congrArg (fun _a ↦ f (i - 1) < f _a) (Nat.sub_add_cancel h₉)) ▸ (hfsi (i - 1) i (by omega) (by omega))
      have h₁₀ : μA μ ⟨(HNFilt n, HNFilt (n+1)), h₃⟩ ≤ μA μ ⟨(f (i-1),f i), h₇⟩ := by
        have h₁₁ := hss (i-1) h₈
        simp [Nat.sub_one_add_one <| ne_of_gt h₉] at h₁₁
        exact le_trans h₆ <| le_of_not_gt (h₁₁.out.choose_spec.2.1 (HNFilt (n + 1) ⊔ f (i - 1)) ⟨le_sup_right,sup_le_iff.2 ⟨(Nat.find_spec h₂).2,le_of_lt h₇⟩⟩ <| ne_of_lt <|right_lt_sup.2 h₄)
      have h₁₂ : i = n + 1 := by
        refine eq_of_ge_of_not_gt h₁₅ ?_
        by_contra!
        have : HNFilt n < f (n+1):= by
          simp only [HNFilt, ← hn]
          apply hfsi n (n+1) (by omega) (by omega)
        have h₁₂ : μA μ ⟨(HNFilt n, HNFilt (n + 1)), h₃⟩ < μA μ ⟨(HNFilt n, f (n+1)),by omega⟩ := by
          have h₁₃ := hmua n (i-1) (by omega) (by omega)
          simp [hn, Nat.sub_one_add_one <| ne_of_gt h₉] at h₁₃
          exact lt_of_le_of_lt h₁₀ h₁₃
        exact ((HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le this le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt this,le_top⟩ <| ne_of_lt this) h₁₂
      have h₁₄ := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg f h₁₂)
      have h₁₉ : HNFilt n < f (n+1) := by
          simp [HNFilt]
          rw [← hn, ← h₁₂]
          nth_rw 1 [h₁₂] at h₇
          exact h₇
      have h₁₆ : f n < HNFilt (n + 1):= Eq.mpr (hn ▸ rfl)
        (is_strict_mono μ n (ne_of_lt (lt_of_lt_of_le h₃ le_top)))
      have h₁₇ := le_of_not_gt <| (hss n (by omega)).out.choose_spec.choose_spec.1 (HNFilt (n+1)) ⟨le_of_lt h₁₆,h₁₄⟩ <| ne_of_lt h₁₆
      simp only [hn] at h₁₇
      exact eq_of_le_of_le ((HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.2 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ (ne_of_lt h₁₉) (eq_of_le_of_not_lt h₁₇ <| (HNFil_prop_of_def μ n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ <| ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [ffst (n+1) (by omega),eq_comm]
      rw [ffst n (by omega)] at hn
      exact not_ne_iff.1 <| (ne_top_iff_lt_len μ (n+1)).not.2 (not_lt_of_ge <| le_of_lt <| Nat.lt_add_one_iff.2 <| le_of_not_lt <| (ne_top_iff_lt_len μ n).not.1 (not_ne_iff.2 hn.symm))


end impl
