import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl
import HarderNarasimhan.Semistability.Defs
import Mathlib.Tactic.Linarith

namespace HarderNarasimhan

namespace impl

lemma prop3d2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
(x : ℒ) (hxI : InIntvl I x)
(z : ℒ) (hzI : InIntvl I z)
(h : x < z)
(h' : μA μ ⟨(x , z) , h⟩ = ⊤)
(a : ℒ) (haI : InIntvl I a) (hax : a < x):
μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩ := by
  have h'' : μA μ ⟨(a , x) , hax⟩ ⊓ μA μ ⟨(x , z) , h⟩ ≤ μA μ ⟨(a,z),lt_trans hax h⟩ := impl.prop2d6₁I I μ hμcvx a haI x hxI z hzI ⟨hax,h⟩
  rw [h', inf_top_eq] at h''
  exact h''


lemma cor3d3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
(h : ∀ f : ℕ → ℒ, (h : ∀ n : ℕ, f n > f (n + 1)) →  ∃N : ℕ, μA μ ⟨(f <| N + 1, f N),h N⟩ = ⊤)
: μA_DescendingChainCondition μ := by
  refine { μ_dcc := fun a f h₁ h₂ ↦ ?_ }
  rcases (h f h₂) with ⟨N, hN⟩
  exact ⟨N,prop3d2 TotIntvl μ hμcvx (f <| N + 1) (in_TotIntvl <| f <| N + 1) (f N) (in_TotIntvl <| f N) (h₂ N) hN a (in_TotIntvl <| a) (h₁ <| N + 1)⟩


def ℒₛ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : {p : ℒ // InIntvl I p}) (hx : I.val.1 ≠ x) : Set ℒ :=
{p : ℒ | ∃ h₁ : InIntvl I p, ∃ h₂ : I.val.1 ≠ p ∧ p < x, μA μ ⟨(I.val.1,p),lt_of_le_of_ne h₁.1 h₂.1⟩ > μA μ ⟨(I.val.1 , x.val) , lt_of_le_of_ne x.prop.1 hx⟩}


noncomputable def prop3d4₀func {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [h :WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(k : ℕ) : {p : ℒ // InIntvl I p} :=
  letI := Classical.propDecidable
  match k with
  | 0 => ⟨I.val.2, ⟨le_of_lt I.prop, le_rfl⟩⟩
  | n+1 =>
    let prev := prop3d4₀func μ I n
    if hbot : I.val.1 = prev.val then
      ⟨I.val.1, ⟨le_rfl,le_of_lt I.prop⟩⟩
    else
      if hne : (ℒₛ μ I prev hbot).Nonempty then
        let res := h.wf.has_min (ℒₛ μ I prev hbot) hne
        ⟨(res).choose,res.choose_spec.1.out.choose⟩
      else
        ⟨I.val.1, ⟨le_rfl,le_of_lt I.prop⟩⟩


lemma prop3d4₀func_helper {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i+1)).val ) :
I.val.1 ≠ (prop3d4₀func μ I i).val := by
  by_contra hcontra
  simp only [prop3d4₀func, hcontra] at hi
  exact hi rfl


lemma prop3d4₀func_defprop1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i+1)).val ) :
μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ > μA μ ⟨(I.val.1 , (prop3d4₀func μ I i).val) , lt_of_le_of_ne ((prop3d4₀func μ I i)).prop.1 <| prop3d4₀func_helper μ I i hi⟩ := by
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra] at hi
    simp at hi
  simp only [hne]
  exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec


lemma prop3d4₀func_defprop2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3: WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i+1)).val ) :
∀ z : ℒ, (hz : (prop3d4₀func μ I (i+1)).val < z ∧ z ≤ (prop3d4₀func μ I i).val) →
    ¬ μA μ ⟨(I.val.1, z),lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1⟩ ≥ μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ := by
  intro z hz
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra] at hi
    simp at hi
  simp only [hne]
  by_contra hcontra
  have h' : z ∈ (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) := by
    use ⟨le_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i + 1)).prop.1 hz.1,le_trans hz.2 (prop3d4₀func μ I i).prop.2⟩
    have h'' : z < (prop3d4₀func μ I i).val := by
      apply lt_of_le_of_ne hz.2
      by_contra hcontra'
      simp [hcontra'] at hcontra
      exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec.not_le hcontra
    use ⟨ne_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1,h''⟩, gt_of_ge_of_gt hcontra.ge (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hne] at hz
  exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.2 z h' hz.1


lemma prop3d4₀func_strict_decreasing {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) :
∀ i : ℕ, I.val.1 ≠ (prop3d4₀func μ I i).val →
(prop3d4₀func μ I i).val > (prop3d4₀func μ I (i+1)).val := by
  intro i hi
  by_cases h: I.val.1 = (prop3d4₀func μ I (i+1)).val
  · simp [prop3d4₀func, hi] at h
    by_cases hne : (ℒₛ μ I (prop3d4₀func μ I i) hi).Nonempty
    · simp [hne] at h
      exact False.elim ((inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) hi) hne).choose_spec.1.out.choose_spec.choose.1 h)
    · simp only [prop3d4₀func, hi, hne]
      exact lt_of_le_of_ne (prop3d4₀func μ I i).prop.1 hi
  · simp only [prop3d4₀func, hi]
    have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i h).Nonempty := by
      by_contra hcontra
      simp only [prop3d4₀func, prop3d4₀func_helper μ I i h, hcontra] at h
      simp at h
    simp only [hne]
    exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) hi) hne).choose_spec.1.out.choose_spec.choose.2


lemma prop3d4₀func_fin_len  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μA_DescendingChainCondition μ) :
∃ i : ℕ, (prop3d4₀func μ I i).val = I.val.1 := by
  by_contra!
  let func := fun m : ℕ => (prop3d4₀func μ I m).val
  have h₀ : ∀ i : ℕ, func i > I.val.1 := by
    intro i
    rw [gt_iff_lt]
    exact Ne.lt_of_le (this i).symm  (prop3d4₀func μ I i).prop.1
  have h₂ := fun t ↦ prop3d4₀func_defprop1 μ I t (this (t + 1)).symm
  rcases (hμDCC.μ_dcc I.val.1 func h₀ fun t ↦ prop3d4₀func_strict_decreasing μ I t (this t).symm) with ⟨N, hN⟩
  exact not_le_of_gt (h₂ N) hN


noncomputable def prop3d4₀func_len  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μA_DescendingChainCondition μ) : ℕ := by
  letI := Classical.propDecidable
  exact Nat.find (prop3d4₀func_fin_len μ I hμDCC)


lemma prop3d4₀func_len_nonzero {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ) :
prop3d4₀func_len μ I hμDCC ≠ 0 := by
  letI := Classical.propDecidable
  by_contra hcontra
  have h : (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC)).val = I.val.1 := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
  simp only [hcontra, prop3d4₀func] at h
  exact (lt_self_iff_false I.val.1).1 (h ▸ I.prop)


lemma prop3d4₀func_defprop3₀ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ)
(i : ℕ) (hi : i < (prop3d4₀func_len μ I hμDCC)) :
I.val.1 < (prop3d4₀func μ I i).val := by
  letI := Classical.propDecidable
  exact ((Nat.find_min (prop3d4₀func_fin_len μ I hμDCC)) hi).decidable_imp_symm fun hcontra ↦ (eq_of_le_of_not_lt (prop3d4₀func μ I i).prop.1 hcontra).symm


lemma prop3d4₀func_defprop3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ)
(y: ℒ) (hy : I.val.1 < y ∧ y ≤ (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) :
¬ μA μ ⟨(I.val.1,y),hy.1⟩ >
  μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) , prop3d4₀func_defprop3₀ μ I hμDCC ((prop3d4₀func_len μ I hμDCC) - 1) <| Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC⟩ := by
  letI := Classical.propDecidable
  let len := prop3d4₀func_len μ I hμDCC
  by_contra hcontra
  by_cases hcases : y < (prop3d4₀func μ I (len - 1)).val
  · have h₂ : (prop3d4₀func μ I len).val = I.val.1 := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
    have h₃ : ¬ (ℒₛ μ I (prop3d4₀func μ I <| len - 1) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))).Nonempty := by
      by_contra hcontra'
      have triv : len - 1 + 1 = len :=  Nat.sub_one_add_one <| prop3d4₀func_len_nonzero μ I hμDCC
      rw [← (triv)] at h₂
      simp only [prop3d4₀func, ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC)] at h₂
      simp [hcontra'] at h₂
      apply (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I (len-1)) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))) hcontra').choose_spec.1.out.choose_spec.choose.1 h₂.symm
    refine h₃ ?_
    use y, ⟨le_of_lt hy.1,le_trans hy.2 (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC - 1)).prop.2⟩, ⟨ne_of_lt hy.1,hcases⟩
  · simp only [eq_of_le_of_not_lt hy.2 hcases] at hcontra
    exact (lt_self_iff_false <| μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| len - 1).val) , prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) <| Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC⟩).1 hcontra


lemma prop3d4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] -- The ascending chain condition. Actually we only need this condition on the Interval I, but to make the life easy, we require it on the whole ℒ.
-- This actually does `NOT` make the statement any weaker, since if we take I to be (⊥,⊤), then we can "apply" this global version to I itself, which is also a sublattice of ℒ.
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμDCC : μA_DescendingChainCondition μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
: (StI μ I).Nonempty := by
  letI := Classical.propDecidable
  let len := prop3d4₀func_len μ I hμDCC
  let func:= prop3d4₀func μ I
  by_cases h : len = 1
  · refine ⟨I.val.2, ⟨le_of_lt I.prop, le_rfl⟩, ne_of_lt I.prop,⟨?_,fun _ hyI _ _ ↦ hyI.2⟩⟩
    intro y hyI hy
    have h' := (congrArg (fun _a ↦ (func (_a - 1)).val = I.val.2) h) ▸ (of_eq_true (eq_self I.val.2))
    have h'' : ¬ μA μ ⟨(I.val.1, y), lt_of_le_of_ne hyI.1 hy⟩ > μA μ ⟨(I.val.1, (func (len-1)).val), prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) <| Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC⟩
        := prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.left hy,h' ▸ hyI.2⟩
    simp [h'] at h''
    exact h''
  · have h₂ : ∀ i : ℕ, i ≤ len -1 → I.val.1 ≠ (func i).val := by
      intro i hi
      by_contra!
      exact (Nat.find_min (prop3d4₀func_fin_len μ I hμDCC) <| Nat.lt_of_le_sub_one (Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC) hi) this.symm
    have h₃ : ∀ i : ℕ, (hi : 1 ≤ i ∧ i ≤ len -1) → (∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → (y < func (i-1) ∧ μA μ ⟨(I.val.1, y), lt_of_le_of_ne hyI.1 hy⟩ ≥ μA μ ⟨(I.val.1, (func i).val), lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩) → y ≤ (func i).val) := by
      intro i hi y hyI hy hy'
      by_contra!
      have h₃' : (func i).val < y ⊔ (func i).val ∧ y ⊔ (func i).val ≤ (func (i-1)).val := by
        refine ⟨right_lt_sup.2 this, sup_le_iff.2 ⟨le_of_lt hy'.1,?_⟩⟩
        have h₃'' : (prop3d4₀func μ I (i - 1)).val > (prop3d4₀func μ I (i - 1 + 1)).val :=
          prop3d4₀func_strict_decreasing μ I (i-1) (h₂ (i-1) <| le_trans (le_of_lt <| Nat.sub_one_lt <| Nat.one_le_iff_ne_zero.1 hi.1) hi.2)
        rw [Nat.sub_one_add_one] at h₃''
        apply le_of_lt h₃''
        exact Nat.one_le_iff_ne_zero.1 hi.1
      have h₃''' : ∀ (hi' : I.val.1 ≠ (func i).val) (z : ℒ) (hz : (func i).val < z ∧ z ≤ (func (i - 1)).val),
        ¬ μA μ ⟨(I.val.1, z), lt_of_le_of_lt (func i).prop.1 hz.1⟩ ≥ μA μ ⟨(I.val.1, (func (i - 1 + 1)).val), lt_of_le_of_ne ((func (i - 1 + 1)).prop).1 ((Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2)⟩ :=
        fun hi' z hz ↦ prop3d4₀func_defprop2 μ I (i - 1) ( (Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2) z ((Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ hz)
      simp [*] at h₃'''
      exact (h₃''' (y ⊔ func i) h₃') <| inf_eq_right.2 hy'.2 ▸ impl.prop2d8₁I I μ hμcvx y hyI (func i) (func i).prop I.val.1 ⟨le_rfl,le_of_lt I.prop⟩  ⟨lt_of_le_of_ne hyI.1 hy,lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩
    have h₄ : ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → μA μ ⟨(I.val.1, y) , lt_of_le_of_ne hyI.1 hy⟩ ≥ μA μ ⟨(I.val.1, (func (len - 1)).val) , lt_of_le_of_ne (func (len - 1)).prop.1 <| h₂ (len - 1) le_rfl⟩ → (∀ i : ℕ, i ≤ len - 1 → y ≤ (func i).val) := by
      intro y hyI hy hy' i hi
      induction' i with i hi'
      · simp only [func,prop3d4₀func]
        exact hyI.2
      · have hfinal : ∀ j : ℕ, (hj : j ≤ len - 1) → μA μ ⟨(I.val.1, (func (len - 1)).val), lt_of_le_of_ne ((func (len - 1)).prop).1 (h₂ (len - 1) le_rfl)⟩ ≥ μA μ ⟨(I.val.1, func j), prop3d4₀func_defprop3₀ μ I hμDCC j <| lt_of_le_of_lt hj <| Nat.sub_one_lt <| ne_of_gt <| Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC⟩
         := by
          apply Nat.decreasingInduction
          · exact fun k hk hk' ↦  le_of_lt <| lt_of_lt_of_le (prop3d4₀func_defprop1 μ I k <| ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (k+1) <| Nat.add_lt_of_lt_sub hk) hk'
          · exact le_rfl
        have hh : y < func i := by
          refine lt_of_le_of_ne (hi' (by linarith)) ?_
          by_contra!
          have hhh :=  gt_of_ge_of_gt hy' <| gt_of_ge_of_gt (hfinal (i+1) hi) <| prop3d4₀func_defprop1 μ I i (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (i+1) <| lt_of_le_of_lt hi <| Nat.sub_one_lt <| ne_of_gt <| Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC)
          simp only [this] at hhh
          exact irrefl _ hhh
        exact h₃ (i+1) ⟨by linarith,hi⟩ y hyI hy ⟨hh,ge_trans hy' (hfinal (i+1) hi)⟩
    use (func (len - 1)).val
    constructor
    · refine ⟨h₂ (len - 1) le_rfl,⟨?_,fun y hyI hy hy' ↦ (fun y hyI hy h ↦ h₄ y hyI hy h (len - 1) le_rfl) y hyI hy <| ge_of_eq hy'⟩⟩
      intro y hyI hy
      by_contra!
      exact prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.1 hy,(fun y hyI hy h ↦ h₄ y hyI hy h (len - 1) le_rfl) y hyI hy <| le_of_lt this⟩ this
    · exact (func (len - 1)).prop


lemma rmk3d5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hySt : y ∈ StI μ I) : x = y := by
  rcases hxSt with ⟨hxI,⟨hx,⟨hxS₁,hxS₂⟩⟩⟩
  rcases hySt with ⟨hyI,⟨hy,⟨hyS₁,hyS₂⟩⟩⟩
  exact eq_of_le_of_le (hyS₂ x hxI hx (eq_of_le_of_le (le_of_not_gt <| hxS₁ y hyI hy) (le_of_not_gt <| hyS₁ x hxI hx)).symm) (hxS₂ y hyI hy <| eq_of_le_of_le (le_of_not_gt <| hxS₁ y hyI hy) (le_of_not_gt <| hyS₁ x hxI hx))


lemma prop3d7₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxSt : x ∈ StI μ I) :
semistableI μ ⟨(I.val.1 , x), lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ := by
  rcases hxSt with ⟨hxI,⟨hx',⟨hx'',hxS₂I⟩⟩⟩
  exact ⟨⟨hxI.1,le_rfl⟩, hx', ⟨fun z hzI hz ↦ hx'' z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz,fun z hzI hz hz' ↦ hxS₂I z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz hz'⟩⟩


lemma prop3d7₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(x : ℒ) (hxSt : x ∈ StI μ I) :
∀ y : ℒ, (hyI : InIntvl I y) → (hy : y > x) → ¬ μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨(x, y), hy⟩ := by
  by_contra!
  rcases this with ⟨y,⟨hyI,⟨hy,hy'⟩⟩⟩
  exact (not_le_of_gt hy) (hxSt.out.choose_spec.choose_spec.2 y hyI (ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hy) <|eq_of_ge_of_not_gt ((inf_eq_left.2 hy') ▸ impl.prop2d6₁I I μ hμcvx I.val.1 ⟨le_rfl,le_of_lt I.prop⟩ x hxSt.out.choose y hyI ⟨lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose,hy⟩) <| hxSt.out.choose_spec.choose_spec.1 y hyI <| ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hy)


lemma prop3d8₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)-- (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
IsTotal (StI μ I) (· ≤ ·) := by
  refine { total := ?_ }
  rintro ⟨x,hx⟩ ⟨x',hx'⟩
  have h₁ : IsComparable (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩) (μA μ ⟨(I.val.1,x'),lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩) ∨ IsAttained μ ⟨(I.val.1 , x ⊔ x') , lt_sup_of_lt_right <| lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩:= by
    cases' h with htotal hattained
    · exact Or.inl <| htotal.total (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩) (μA μ ⟨(I.val.1,x'),lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩)
    · exact Or.inr <| hattained  (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩ <| ne_of_lt <| lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose
  have h₂ : μA μ ⟨(I.val.1, x), lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩ = μA μ ⟨(I.val.1, x ⊔ x'), lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩ ∨ μA μ ⟨(I.val.1, x'), lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩ = μA μ ⟨(I.val.1, x ⊔ x'), lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩ := by
    cases' (impl.prop2d8₂I I μ hμcvx x hx.out.choose x' hx'.out.choose I.val.1 ⟨le_rfl,le_of_lt I.prop⟩ ⟨lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose,lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩ h₁) with c1 c2
    · exact Or.inl <| eq_of_le_of_not_lt c1 <| hx.out.choose_spec.choose_spec.1 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩ <| ne_of_lt <| lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose
    · exact Or.inr <| eq_of_le_of_not_lt c2 <| hx'.out.choose_spec.choose_spec.1 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩ <| ne_of_lt <| lt_sup_of_lt_right <| lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose
  have h₃ : x ⊔ x' ≤ x ∨ x ⊔ x' ≤ x' := by
    cases' h₂ with c1 c2
    · exact Or.inl <| hx.out.choose_spec.choose_spec.2 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩  (ne_of_lt <| lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose) c1.symm
    · exact Or.inr <| hx'.out.choose_spec.choose_spec.2 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩  (ne_of_lt <| lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose) c2.symm
  cases' h₃ with c1 c2
  · exact Or.inr (sup_le_iff.1 c1).2
  · exact Or.inl (sup_le_iff.1 c2).1


lemma prop3d8₁' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ]  [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)  :
∃ s : ℒ, IsGreatest (StI μ I) s := by
  rcases inst_3.wf.has_min (StI μ I) (prop3d4 μ hμ I hμcvx) with ⟨M,hM⟩
  refine ⟨M,⟨hM.1,mem_upperBounds.2 ?_⟩⟩
  intro x hx
  cases' (prop3d8₁ μ I hμcvx h).total ⟨x, hx⟩ ⟨M, hM.1⟩ with c1 c2
  · exact c1
  · exact le_of_eq <| eq_of_ge_of_not_gt c2 (hM.2 x hx)


lemma prop3d8₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)-- (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hyI : InIntvl I y)
(hxy : x < y) :
μA μ ⟨(I.val.1 , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩ := by
  have h : IsComparable (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩) (μA μ ⟨(x,y), hxy⟩) ∨ IsAttained μ ⟨(I.val.1,y),lt_of_le_of_lt hxSt.out.choose.1 hxy⟩:= by
    cases' h with htotal hattained
    · exact Or.inl <| htotal.total (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩) (μA μ ⟨(x,y), hxy⟩)
    · exact Or.inr <| hattained y hyI (ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hxy)
  cases' (impl.prop2d6₃I I μ hμcvx I.val.1 ⟨le_rfl,le_of_lt I.prop⟩ x hxSt.out.choose y hyI ⟨lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose,hxy⟩ h) with c1 c2
  · exact c1.symm
  · exact False.elim  ((not_lt_of_le <| hxSt.out.choose_spec.choose_spec.2 y hyI  (ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hxy) <| eq_of_ge_of_not_gt c2.1 (hxSt.out.choose_spec.choose_spec.1 y hyI <| ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hxy)) hxy)


theorem semistable_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
  Semistable μ ↔ semistableI μ TotIntvl := by
  simp [semistableI, TotIntvl,StI,S₁I,S₂I]
  constructor
  · intro h
    use in_TotIntvl _
    exact fun y hyI hy ↦ h.semistable y <| Ne.symm hy
  · exact fun h ↦ {semistable := fun y hyI hy ↦ (h.choose_spec y (in_TotIntvl _) (Ne.symm hyI)) hy}


lemma stupid_helper {α : Type} {a b c d: α} (h : a = b) (h' : b = c) (h'' : c = d) : a = d := h ▸ h' ▸ h''


theorem semistableI_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : semistableI μ I ↔ Semistable (Resμ I μ) := by
  rw [semistable_iff]
  unfold Resμ
  constructor
  · intro h
    simp [semistableI]
    simp [semistableI] at h
    rcases h.out with ⟨h1,h2,h3,h4⟩
    apply Set.mem_def.2
    refine Set.setOf_app_iff.mpr ?_
    use in_TotIntvl (TotIntvl.val).2
    use ne_of_lt (TotIntvl.prop)
    constructor
    · simp [S₁I] at *
      intro y hyI hy
      have := h3 y hyI (Subtype.coe_ne_coe.2 hy)
      by_contra fuck
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq fuck ?_)
      · simp [μA]
        congr 1
        ext
        simp only [Set.mem_setOf_eq, Subtype.coe_mk]
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,ha1.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          simp only [Set.mem_setOf_eq, Subtype.coe_mk]
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            exact ⟨b.val, ⟨⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩,rfl⟩⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩
            constructor
            · rfl
            · exact ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · rintro ⟨b,⟨hb1,hb2⟩⟩
          rw [← hb2]
          use b
          refine ⟨⟨hb1.1,?_⟩,?_⟩
          · by_contra h'
            exact hb1.2 <| Subtype.coe_eq_of_eq_mk h'
          · simp [μmax]
            congr 1; ext
            constructor
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use ⟨c,⟨le_trans b.prop.1 hc1.1.1,hc1.1.2⟩⟩, ⟨hc1.1,Subtype.coe_ne_coe.1 hc1.2⟩
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use c.val, ⟨hc1.1,Subtype.coe_ne_coe.2 hc1.2⟩
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            simp
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 y.prop.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
    · simp [S₂I] at *
      intro y hyI hy h
      refine h4 y hyI (Subtype.coe_ne_coe.2 hy) <| stupid_helper ?_ h ?_
      · simp [μA]
        congr 1; ext
        constructor
        . intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 y.prop.2⟩⟩, ⟨⟨((in_TotIntvl _).1),ha1.1.2⟩,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            simp
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
      · simp [μA]
        congr 1; ext
        constructor
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,ha1.1.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
  · rintro ⟨h1,⟨h3,⟨h4,h5⟩⟩⟩
    simp [semistableI,StI]
    use ⟨le_of_lt I.prop,le_rfl⟩, ne_of_lt I.prop
    constructor
    · simp [S₁I] at *
      intro y hyI hy
      have := h4 ⟨y,hyI⟩ (in_TotIntvl _) (Subtype.coe_ne_coe.1 hy)
      by_contra h
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq h ?_)
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans a.prop.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,ha1.1.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 hyI.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
    · simp [S₂I] at *
      intro y hyI hy h
      refine h5 ⟨y,hyI⟩ (in_TotIntvl _) (Subtype.coe_ne_coe.1 hy) ?_
      refine stupid_helper ?_ h ?_
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans a.prop.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 hyI.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,ha1.1⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩


end impl

end HarderNarasimhan
