import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl


def μDCC {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → (h₂ : ∀ n : ℕ, f n > f (n + 1)) →  ∃ N : ℕ, μA μ ⟨(a, f <| N + 1), h₁ <| N + 1⟩ ≤ μA μ ⟨(a, f N), h₁ N⟩


lemma prop3d2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
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
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
(h : ∀ f : ℕ → ℒ, (h : ∀ n : ℕ, f n > f (n + 1)) →  ∃N : ℕ, μA μ ⟨(f <| N + 1, f N),h N⟩ = ⊤)
: μDCC μ := by
  intro a f h₁ h₂
  rcases (h f h₂) with ⟨N, hN⟩
  use N
  exact prop3d2 TotIntvl μ hμcvx (f <| N + 1) (in_TotIntvl <| f <| N + 1) (f N) (in_TotIntvl <| f N) (h₂ N) hN a (in_TotIntvl <| a) (h₁ <| N + 1)


def S₁I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ > μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩ → y ≤ x


def S₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x)  (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ = μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.1 hx⟩ → y ≤ x


def St {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Set ℒ :=
{l : ℒ | ∃ hlI : InIntvl I l , ∃ hl : I.val.1 ≠ l ,  (S₁I μ I l hlI hl) ∧ (S₂I μ I l hlI hl)}


def ℒₛ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : {p : ℒ // InIntvl I p}) (hx : I.val.1 ≠ x) : Set ℒ :=
{p : ℒ | ∃ h₁ : InIntvl I p, ∃ h₂ : I.val.1 ≠ p ∧ p < x, μA μ ⟨(I.val.1,p),lt_of_le_of_ne h₁.1 h₂.1⟩ > μA μ ⟨(I.val.1 , x.val) , lt_of_le_of_ne x.prop.1 hx⟩}


noncomputable def prop3d4₀func {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
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
        have h: WellFoundedGT ℒ := by
          expose_names
          exact inst_3
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
  simp only [prop3d4₀func] at hi
  simp only [hcontra] at hi
  exact hi rfl


lemma prop3d4₀func_defprop1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i+1)).val ) :
μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ > μA μ ⟨(I.val.1 , (prop3d4₀func μ I i).val) , lt_of_le_of_ne ((prop3d4₀func μ I i)).prop.1 <| prop3d4₀func_helper μ I i hi⟩ := by
  expose_names
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi] at hi
    simp only [hcontra] at hi
    simp at hi
  simp only [hne]
  exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec


lemma prop3d4₀func_defprop2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i+1)).val ) :
∀ z : ℒ, (hz : (prop3d4₀func μ I (i+1)).val < z ∧ z ≤ (prop3d4₀func μ I i).val) →
    ¬ μA μ ⟨(I.val.1, z),lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1⟩ ≥ μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ := by
  expose_names
  intro z hz
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  simp
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi] at hi
    simp only [hcontra] at hi
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
    use ⟨ne_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1,h''⟩
    exact gt_of_ge_of_gt hcontra.ge (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi] at hz
  simp [hne] at hz
  exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne).choose_spec.2 z h' hz.1


lemma prop3d4₀func_strict_decreasing {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) :
∀ i : ℕ, I.val.1 ≠ (prop3d4₀func μ I i).val →
(prop3d4₀func μ I i).val > (prop3d4₀func μ I (i+1)).val := by
  intro i hi
  expose_names
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
(hμDCC : μDCC μ) :
∃ i : ℕ, (prop3d4₀func μ I i).val = I.val.1 := by
  by_contra!
  let func := fun m : ℕ => (prop3d4₀func μ I m).val
  have h₀ : ∀ i : ℕ, func i > I.val.1 := by
    intro i
    rw [gt_iff_lt]
    exact Ne.lt_of_le (this i).symm  (prop3d4₀func μ I i).prop.1
  have h₁ : ∀ i : ℕ, func i > func (i+1) :=
    fun t ↦ prop3d4₀func_strict_decreasing μ I t (this t).symm
  have h₂ : ∀ i : ℕ,
    μA μ ⟨(I.val.1 , func (i+1)) , h₀ (i+1)⟩ >
    μA μ ⟨(I.val.1 , func i) , h₀ i⟩ :=
      fun t ↦ prop3d4₀func_defprop1 μ I t (this (t + 1)).symm
  rcases (hμDCC I.val.1 func h₀ h₁) with ⟨N, hN⟩
  exact not_le_of_gt (h₂ N) hN


noncomputable def prop3d4₀func_len  {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μDCC μ) : ℕ := by
  letI := Classical.propDecidable
  exact Nat.find (prop3d4₀func_fin_len μ I hμDCC)


lemma prop3d4₀func_len_nonzero {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μDCC μ) :
prop3d4₀func_len μ I hμDCC ≠ 0 := by
  letI := Classical.propDecidable
  by_contra hcontra
  have h : (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC)).val = I.val.1 := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
  simp only [hcontra, prop3d4₀func] at h
  exact (lt_self_iff_false I.val.1).1 (h ▸ I.prop)


lemma prop3d4₀func_defprop3₀ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μDCC μ)
(i : ℕ) (hi : i < (prop3d4₀func_len μ I hμDCC)) :
I.val.1 < (prop3d4₀func μ I i).val := by
  letI := Classical.propDecidable
  apply ((Nat.find_min (prop3d4₀func_fin_len μ I hμDCC)) hi).decidable_imp_symm
  intro hcontra
  apply (eq_of_le_of_not_lt (prop3d4₀func μ I i).prop.1 hcontra).symm


lemma prop3d4₀func_defprop3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μDCC μ)
(y: ℒ) (hy : I.val.1 < y ∧ y ≤ (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) :
¬ μA μ ⟨(I.val.1,y),hy.1⟩ >
  μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) , prop3d4₀func_defprop3₀ μ I hμDCC ((prop3d4₀func_len μ I hμDCC) - 1) <| Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC⟩ := by
  letI := Classical.propDecidable
  expose_names
  let len := prop3d4₀func_len μ I hμDCC
  by_contra hcontra
  by_cases hcases : y < ↑(prop3d4₀func μ I (len - 1))
  · have h₁ : (ℒₛ μ I (prop3d4₀func μ I <| len - 1) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))).Nonempty := by
      use y
      use ⟨le_of_lt hy.1,le_trans hy.2 (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC - 1)).prop.2⟩
      use ⟨ne_of_lt hy.1,hcases⟩
    have h₂ : (prop3d4₀func μ I len).val = I.val.1 := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
    have h₃ : ¬ (ℒₛ μ I (prop3d4₀func μ I <| len - 1) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))).Nonempty := by
      by_contra hcontra'
      have triv : len - 1 + 1 = len := by
         exact Nat.sub_one_add_one <| prop3d4₀func_len_nonzero μ I hμDCC
      rw [← triv] at h₂
      simp only [prop3d4₀func] at h₂
      simp only [ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC)] at h₂
      simp [hcontra'] at h₂
      apply (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I (len-1)) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))) hcontra').choose_spec.1.out.choose_spec.choose.1 h₂.symm
    exact h₃ h₁
  · simp only [eq_of_le_of_not_lt hy.2 hcases] at hcontra
    exact (lt_self_iff_false <| μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| len - 1).val) , prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) <| Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC⟩).1 hcontra


lemma prop3d4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] -- The ascending chain condition. Actually we only need this condition on the Interval I, but to make the life easy, we require it on the whole ℒ.
-- This actually does `NOT` make the statement any weaker, since if we take I to be (⊥,⊤), then we can "apply" this global version to I itself, which is also a sublattice of ℒ.
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μDCC μ) : (St μ I).Nonempty := by
  sorry


lemma rmk3d5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S] [LinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x)
(hxS₁ : S₁I μ I x hxI hx)
(hxS₂ : S₂I μ I x hxI hx)
(y : ℒ) (hyI : InIntvl I y) (hy : I.val.1 ≠ y)
(hyS₁ : S₁I μ I y hyI hy)
(hyS₂ : S₂I μ I y hyI hy) : x = y := sorry


def semistableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := I.val.2 ∈ St μ I


def stableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
semistableI μ I ∧ ∀ x : ℒ, (hxI : InIntvl I x) → (hx : x ≠ I.val.1) → μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx.symm⟩ ≠ μA μ ⟨(I.val.1 , I.val.2) , I.prop⟩


lemma prop3d7 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hx : x ≠ I.val.2)
(hxSt : x ∈ St μ I) :
semistableI μ ⟨(I.val.1 , x), lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ∧
∀ y : ℒ, (hyI : InIntvl I y) → (hy : y > x) → ¬ μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨(x, y), hy⟩ := sorry


lemma prop3d8₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
IsTotal (St μ I) (· ≤ ·) := sorry


lemma prop3d8₁' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ]  [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
∃ s : ℒ, IsGreatest (St μ I) s := by
expose_names
rcases inst_3.wf.has_min (St μ I) (prop3d4 μ I hμ) with ⟨M,hM⟩
use M
constructor
exact hM.1
refine mem_upperBounds.2 ?_
intro x hx
cases' (prop3d8₁ μ hμ I h).total ⟨x, hx⟩ ⟨M, hM.1⟩ with c1 c2
· exact c1
· simp at c2
  apply le_of_eq
  apply eq_of_ge_of_not_gt c2 (hM.2 x hx)


lemma prop3d8₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)
(x : ℒ) (hxSt : x ∈ St μ I)
(y : ℒ) (hyI : InIntvl I y)
(hxy : x < y) :
μA μ ⟨(I.val.1 , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩ := sorry
