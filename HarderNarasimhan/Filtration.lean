import HarderNarasimhan.Semistability.Results

namespace Filtration
noncomputable def HNFil {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I)
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNFil μ hμ hμcvx h n
    letI := Classical.propDecidable
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨(prev_term , ⊤) , lt_top_iff_ne_top.2 htop⟩ : {p : ℒ × ℒ // p.1 < p.2})
      (impl.prop3d8₁' μ hμ I' (Convex_of_Convex_large ⟨(⊥ ,⊤) , bot_lt_top⟩ I' ⟨bot_le,le_top⟩ μ hμcvx) (Or.casesOn
       h (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨(I'.val.1 , z) ,  lt_of_le_of_ne hzI.left hz⟩)).choose


lemma HNFil_defprop {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
∀ n : Nat, (h' : HNFil μ hμ hμcvx h n ≠ ⊤) → IsGreatest (StI μ ⟨(HNFil μ hμ hμcvx h n , ⊤), lt_top_iff_ne_top.2 h'⟩) (HNFil μ hμ hμcvx h (n + 1)) := by
  intro n h'
  simp only [HNFil, h']
  exact (HNFil._proof_4 μ hμ hμcvx h n h').choose_spec


lemma is_srtrict_mono {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
∀ n : Nat, HNFil μ hμ hμcvx h n ≠ ⊤ → HNFil μ hμ hμcvx h n < HNFil μ hμ hμcvx h (n + 1) := fun
    n hn ↦ lt_of_le_of_ne (HNFil_defprop μ hμ hμcvx h n hn).1.1.1 (HNFil_defprop μ hμ hμcvx h n hn).1.2.1


lemma of_finite_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I)
: ∃ N : Nat, HNFil μ hμ hμcvx h N = ⊤ := by
  by_contra!
  expose_names
  exact (WellFounded.wellFounded_iff_no_descending_seq.1 inst_3.wf).elim ⟨fun n => HNFil μ hμ hμcvx h n, fun n => is_srtrict_mono μ hμ hμcvx h n (this n)⟩


noncomputable def HNlen {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) : Nat := by
  letI := Classical.propDecidable
  exact Nat.find (of_finite_len μ hμ hμcvx h)


lemma ne_top_iff_lt_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
  ∀ n : Nat, HNFil μ hμ hμcvx h n ≠ ⊤ ↔ n < HNlen μ hμ hμcvx h := by
  letI := Classical.propDecidable
  intro n
  constructor
  · intro hn
    by_contra!
    have h : ∀ n : ℕ, (hn' : HNlen μ hμ hμcvx h ≤ n) → HNFil μ hμ hμcvx h n = ⊤ := by
      apply Nat.le_induction
      · exact Nat.find_spec (of_finite_len μ hμ hμcvx h)
      · intro k hk hk'
        simp [HNFil,hk']
    exact hn (h n this)
  · exact fun hn ↦ Nat.find_min (of_finite_len μ hμ hμcvx h) hn


open Classical

theorem thm3d10  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLinearOrder S] (hS : IsTotal S (· ≤ ·))
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvex μ)
(f : ℕ → ℒ) (hf0 : f 0 = ⊥)
(hffin : ∃ n : ℕ, f n = ⊤)
(hfsi : ∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ Nat.find hffin → f i < f j)
--(hfsi : ∀ i : ℕ, i < Nat.find hffin → f i < f (i + 1))
(ffst : ∀ i : ℕ, i ≥ Nat.find hffin → f i = ⊤)
(hss : ∀ j : ℕ, (hj : j < Nat.find hffin) → semistableI μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩)
(hmua: ∀ i : ℕ, ∀ j : ℕ, (hij : i < j) → (hj : j + 1 ≤ Nat.find hffin) → μA μ ⟨(f i, f (i+1)), hfsi i (i+1) (lt_add_one i) <| (by omega)⟩ > μA μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) <| (by omega)⟩)
: f = HNFil μ hμ hμcvx (Or.inl hS) := by
  let HNFilt := HNFil μ hμ hμcvx (Or.inl hS)
  funext k
  induction' k with n hn
  · simp only [hf0, HNFil]
  · by_cases h₁ : n + 1 ≤ Nat.find hffin
    · have h₂ : ∃ N : ℕ, N ≥ (n+1) ∧ HNFilt (n+1) ≤ f N := by
        use (Nat.find hffin)
        constructor
        · exact h₁
        · simp [ffst]
      let i : ℕ := Nat.find h₂
      have h₃ : HNFil μ hμ hμcvx (Or.inl hS) n < HNFil μ hμ hμcvx (Or.inl hS) (n + 1)
            := (is_srtrict_mono μ hμ hμcvx (Or.inl hS) n <| Nat.find_min (of_finite_len μ hμ hμcvx (Or.inl hS)) <| lt_of_lt_of_le (lt_add_one n) <| Nat.add_one_le_iff.2 ((ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) n).mp (Eq.rec (motive := fun x h ↦ n < Nat.find hffin → ¬x = ⊤) (Nat.find_min hffin) hn (lt_of_lt_of_le (lt_add_one n) h₁))))
      have h₄ : ¬ HNFilt (n+1) ≤ f (i-1) := by
        have h₅ : ¬(Nat.find h₂ - 1 ≥ n + 1 ∧ HNFilt (n + 1) ≤ f (Nat.find h₂ - 1)) := Nat.find_min h₂ (Nat.sub_one_lt <| ne_of_gt <| lt_of_lt_of_le (Nat.add_one_pos n) (Nat.find_spec h₂).1 )
        apply not_and_or.1 at h₅
        cases' h₅ with h₅ h₅
        · simp at h₅
          apply not_le_of_lt
          rw [← hn] at h₃
          nth_rw 1 [← eq_of_le_of_le (Nat.le_of_lt_add_one h₅) (Nat.sub_le_sub_right (Nat.find_spec h₂).1 1)] at h₃
          exact h₃
        · exact h₅
      have h₁₃ : HNFilt n ≤ f (i - 1) := by
        simp only [HNFilt]
        rw [← hn]
        have : i ≥ n + 1 := (Nat.find_spec h₂).1
        have h₁₄ : n ≤ i - 1 := by omega
        rw [le_iff_eq_or_lt] at h₁₄
        cases' h₁₄ with h₁₄ h₁₄
        · rw [h₁₄]
        · apply le_of_lt
          refine hfsi n (i-1) h₁₄ ?_
          have : i ≤ Nat.find hffin := by
            by_contra!
            cases' not_and_or.1 <| Nat.find_min h₂ this with c₁ c₂
            · exact c₁ h₁
            · simp [Nat.find_spec hffin] at c₂
          omega
      have h₆ : μA μ ⟨(HNFilt n, HNFilt (n+1)), h₃⟩ ≤ μA μ ⟨(f (i-1), (HNFilt (n+1)) ⊔ (f (i-1))), right_lt_sup.2 h₄⟩ := by
        apply impl.lem2d4₃I TotIntvl μ hμcvx (HNFilt (n + 1)) (in_TotIntvl (HNFilt (n + 1))) (f (i - 1)) (in_TotIntvl (f (i - 1))) h₄ (HNFilt n) <| le_inf (le_of_lt h₃) h₁₃
      have h₉ : i > 0 := by
          have : i ≥ n + 1 := (Nat.find_spec h₂).1
          omega
      have h₈ : i - 1 < Nat.find hffin := by
        apply Nat.sub_one_lt_of_le h₉
        by_contra!
        cases' not_and_or.1 <| Nat.find_min h₂ this with c₁ c₂
        · exact c₁ h₁
        · simp [Nat.find_spec hffin] at c₂
      have h₇ : f (i-1) < f i := (congrArg (fun _a ↦ f (i - 1) < f _a) (Nat.sub_add_cancel h₉)) ▸ (hfsi (i - 1) i (by omega) (by omega))
      have h₁₀ : μA μ ⟨(HNFilt n, HNFilt (n+1)), h₃⟩ ≤ μA μ ⟨(f (i-1),f i), h₇⟩ := by
        have h₁₁ : semistableI μ ⟨(f (i - 1), f (i - 1 + 1)), (Nat.sub_one_add_one <|ne_of_gt h₉) ▸ hfsi (i - 1) i (by omega) (by omega)⟩ := hss (i-1) h₈
        simp [Nat.sub_one_add_one <| ne_of_gt h₉] at h₁₁
        exact le_trans h₆ <| le_of_not_gt (h₁₁.out.choose_spec.2.1 (HNFilt (n + 1) ⊔ f (i - 1)) ⟨le_sup_right,sup_le_iff.2 ⟨(Nat.find_spec h₂).2,le_of_lt h₇⟩⟩ <| ne_of_lt <|right_lt_sup.2 h₄)
      have h₁₂ : i = n + 1 := by
        refine eq_of_ge_of_not_gt (Nat.find_spec h₂).1 ?_
        by_contra!
        have : HNFilt n < f (n+1):= by
          simp only [HNFilt, ← hn]
          apply hfsi n (n+1) (by omega) (by omega)
        have h₁₂ : μA μ ⟨(HNFilt n, HNFilt (n + 1)), h₃⟩ < μA μ ⟨(HNFilt n, f (n+1)),by omega⟩ := by
          refine lt_of_le_of_lt h₁₀ ?_
          have h₁₃: μA μ ⟨(f n, f (n + 1)), hn ▸ this⟩ > μA μ ⟨(f (i - 1), f (i - 1 + 1)), hfsi (i - 1) (i - 1 + 1) (lt_add_one (i - 1)) (by omega)⟩ := hmua n (i-1) (by omega) (by omega)
          simp [hn, Nat.sub_one_add_one <| ne_of_gt h₉] at h₁₃
          exact h₁₃
        exact ((HNFil_defprop μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le this le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt this,le_top⟩ <| ne_of_lt this) h₁₂
      have h₁₄ : HNFilt (n+1) ≤ f (n+1) := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg f h₁₂)
      have h₁₅ : μA μ ⟨(HNFilt n, HNFilt (n + 1)), h₃⟩ ≤ μA μ ⟨(HNFilt n, f (n+1)),(congrArg (fun x ↦ x < f (n + 1)) (Eq.trans (congrArg f (add_tsub_cancel_right n 1)) hn)) ▸ ((congrArg (fun _a ↦ f (_a - 1) < f _a) h₁₂) ▸ h₇)⟩ := by
        have h₁₆ : f n < HNFilt (n + 1):= by
          rw [hn]
          exact is_srtrict_mono μ hμ hμcvx (Or.inl hS) n (ne_of_lt <| lt_of_lt_of_le h₃ le_top)
        have h₁₇ : μA μ ⟨(f n, HNFilt (n + 1)), h₁₆⟩ ≤ μA μ ⟨(f n, f (n + 1)), hfsi n (n+1) (lt_add_one n) h₁⟩ := le_of_not_gt <| (hss n (by omega)).out.choose_spec.choose_spec.1 (HNFilt (n+1)) ⟨le_of_lt h₁₆,h₁₄⟩ <| ne_of_lt h₁₆
        simp only [hn] at h₁₇
        exact h₁₇
      have h₁₉ : HNFilt n < f (n+1) := by
          simp [HNFilt]
          rw [← hn, ← h₁₂]
          nth_rw 1 [h₁₂] at h₇
          exact h₇
      exact eq_of_le_of_le ((HNFil_defprop μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.2 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ (ne_of_lt h₁₉) (eq_of_le_of_not_lt h₁₅ <| (HNFil_defprop μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ <| ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [ffst (n+1) (by omega),eq_comm]
      rw [ffst n (by omega)] at hn
      exact not_ne_iff.1 <| (ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) (n+1)).not.2 (not_lt_of_ge <| le_of_lt <| Nat.lt_add_one_iff.2 <| le_of_not_lt <| (ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) n).not.1 (not_ne_iff.2 hn.symm))

end Filtration
