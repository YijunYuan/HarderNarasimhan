import HarderNarasimhan.Filtration.Defs

open Classical

theorem theorem_3_10  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLinearOrder S] (hS : IsTotal S (· ≤ ·))
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(f : ℕ → ℒ) (hf0 : f 0 = ⊥)
(hffin : ∃ n : ℕ, f n = ⊤)
(hfsi : ∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ Nat.find hffin → f i < f j)
--(hfsi : ∀ i : ℕ, i < Nat.find hffin → f i < f (i + 1))
(ffst : ∀ i : ℕ, i ≥ Nat.find hffin → f i = ⊤)
(hss : ∀ j : ℕ, (hj : j < Nat.find hffin) → semistableI μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) hj⟩)
(hmua: ∀ i : ℕ, ∀ j : ℕ, (hij : i < j) → (hj : j + 1 ≤ Nat.find hffin) → μA μ ⟨(f i, f (i+1)), hfsi i (i+1) (lt_add_one i) <| (by omega)⟩ > μA μ ⟨(f j, f (j+1)), hfsi j (j+1) (lt_add_one j) <| (by omega)⟩)
: f = Filtration.HNFil μ hμ hμcvx (Or.inl hS) := by
  let HNFilt := Filtration.HNFil μ hμ hμcvx (Or.inl hS)
  funext k
  induction' k with n hn
  · simp only [hf0, Filtration.HNFil]
  · by_cases h₁ : n + 1 ≤ Nat.find hffin
    · have h₂ : ∃ N : ℕ, N ≥ (n+1) ∧ HNFilt (n+1) ≤ f N := ⟨Nat.find hffin, h₁, by simp [ffst]⟩
      let i : ℕ := Nat.find h₂
      have h₃ := (Filtration.is_strict_mono μ hμ hμcvx (Or.inl hS) n <| Nat.find_min (Filtration.of_fin_len μ hμ hμcvx (Or.inl hS)) <| lt_of_lt_of_le (lt_add_one n) <| Nat.add_one_le_iff.2 ((Filtration.ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) n).mp (Eq.rec (motive := fun x h ↦ n < Nat.find hffin → ¬x = ⊤) (Nat.find_min hffin) hn (lt_of_lt_of_le (lt_add_one n) h₁))))
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
        exact ((Filtration.HNFil_prop_of_def μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le this le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt this,le_top⟩ <| ne_of_lt this) h₁₂
      have h₁₄ := le_of_le_of_eq (Nat.find_spec h₂).2 (congrArg f h₁₂)
      have h₁₉ : HNFilt n < f (n+1) := by
          simp [HNFilt]
          rw [← hn, ← h₁₂]
          nth_rw 1 [h₁₂] at h₇
          exact h₇
      have h₁₆ : f n < HNFilt (n + 1):= Eq.mpr (hn ▸ rfl)
        (Filtration.is_strict_mono μ hμ hμcvx (Or.inl hS) n (ne_of_lt (lt_of_lt_of_le h₃ le_top)))
      have h₁₇ := le_of_not_gt <| (hss n (by omega)).out.choose_spec.choose_spec.1 (HNFilt (n+1)) ⟨le_of_lt h₁₆,h₁₄⟩ <| ne_of_lt h₁₆
      simp only [hn] at h₁₇
      exact eq_of_le_of_le ((Filtration.HNFil_prop_of_def μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.2 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ (ne_of_lt h₁₉) (eq_of_le_of_not_lt h₁₇ <| (Filtration.HNFil_prop_of_def μ hμ hμcvx (Or.inl hS) n <| ne_of_lt <| lt_of_lt_of_le h₃ le_top).1.out.choose_spec.choose_spec.1 (f (n+1)) ⟨le_of_lt h₁₉,le_top⟩ <| ne_of_lt h₁₉).symm) h₁₄
    · apply Nat.gt_of_not_le at h₁
      rw [ffst (n+1) (by omega),eq_comm]
      rw [ffst n (by omega)] at hn
      exact not_ne_iff.1 <| (Filtration.ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) (n+1)).not.2 (not_lt_of_ge <| le_of_lt <| Nat.lt_add_one_iff.2 <| le_of_not_lt <| (Filtration.ne_top_iff_lt_len μ hμ hμcvx (Or.inl hS) n).not.1 (not_ne_iff.2 hn.symm))
