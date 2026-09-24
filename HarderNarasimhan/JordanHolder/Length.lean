/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolder.Defs
public import HarderNarasimhan.PayoffFunction.Convex
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Uniqueness of the length of Jordan–Hölder filtrations

For a semistable slope-like affine payoff function on a modular lattice with values in a
complete linear order, any two Jordan–Hölder filtrations have the same length, under the chain
conditions and finite total payoff hypothesis used in `HarderNarasimhan/JordanHolder/Exists.lean`.

The proof compares two filtrations after restricting to the interval from the last
nonbottom term of one filtration to `⊤`. Joining the other filtration with this term
preserves the payoff conditions on its strict steps and introduces a repeated value.
Removing repeated values gives a shorter filtration, to which induction applies.

## Main results

* `HarderNarasimhan.PayoffFunction.JordanHolderFiltration.length_eq`: any two
  Jordan–Hölder filtrations have the same length.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

/-!
### Removing repeated values from an antitone chain

An antitone chain that reaches `⊥` has only finitely many distinct values. Selecting the
first index of each new value gives a strictly decreasing chain with the same strict steps.
-/

section SubseqIdx

variable {ℒ : Type*} [PartialOrder ℒ] [OrderBot ℒ]

/-- For an antitone `f` that eventually hits `⊥`, from any index `n` with `f n ≠ ⊥` there
is a later index where `f` drops strictly. -/
private lemma exists_next_lt (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (n : ℕ)
    (hcond : f n ≠ ⊥) : ∃ k : ℕ, n < k ∧ f k < f n := by
  let m := Max.max (n + 1) atf.choose
  refine ⟨m, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _), ?_⟩
  have hm : f m = ⊥ := le_bot_iff.mp <| atf.choose_spec ▸ hf (le_max_right _ _)
  simpa [hm] using bot_lt_iff_ne_bot.2 hcond

open Classical in
/-- The indices of the first occurrences of successive distinct values of `f`.
After the selected value reaches `⊥`, the indices increase by one at each step. -/
private noncomputable def subseqIdx (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      if hcond : f (subseqIdx f atf hf t) = ⊥ then subseqIdx f atf hf t + 1
      else Nat.find (exists_next_lt f atf hf (subseqIdx f atf hf t) hcond)

/-- A selected value above `⊥` is followed by a strictly smaller value. -/
private lemma subseqIdx.next_exists (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    (t : ℕ) (hcond : f (subseqIdx f atf hf t) ≠ ⊥) :
    ∃ k : ℕ, subseqIdx f atf hf t < k ∧ f k < f (subseqIdx f atf hf t) :=
  exists_next_lt f atf hf (subseqIdx f atf hf t) hcond

open Classical in
private lemma subseqIdx.succ_eq_find (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    (t : ℕ) (hcond : f (subseqIdx f atf hf t) ≠ ⊥) :
    subseqIdx f atf hf (t + 1) = Nat.find (subseqIdx.next_exists f atf hf t hcond) := by
  simp [subseqIdx, hcond]

open Classical in
private lemma subseqIdx.lt_succ (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) (t : ℕ) :
    subseqIdx f atf hf t < subseqIdx f atf hf (t + 1) := by
  by_cases hcond : f (subseqIdx f atf hf t) = ⊥
  · simp [subseqIdx, hcond]
  · rw [subseqIdx.succ_eq_find f atf hf t hcond]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hf t hcond)).1

private lemma subseqIdx.ge_self (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ∀ n : ℕ, n ≤ subseqIdx f atf hf n :=
  (strictMono_nat_of_lt_succ (subseqIdx.lt_succ f atf hf)).id_le

open Classical in
/-- Between two consecutive selected indices, the chain is constant. -/
private lemma subseqIdx.const_between (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    (i m : ℕ) (hleft : subseqIdx f atf hf i ≤ m) (hright : m < subseqIdx f atf hf (i + 1)) :
    f m = f (subseqIdx f atf hf i) := by
  by_cases hbot : f (subseqIdx f atf hf i) = ⊥
  · apply le_antisymm (hf hleft)
    simp [hbot]
  · apply eq_of_le_of_not_lt (hf hleft)
    intro hdrop
    have hstrict : subseqIdx f atf hf i < m :=
      hleft.lt_of_ne fun heq ↦ hdrop.ne (congrArg f heq).symm
    have hfirst := Nat.find_min' (subseqIdx.next_exists f atf hf i hbot) ⟨hstrict, hdrop⟩
    rw [← subseqIdx.succ_eq_find f atf hf i hbot] at hfirst
    exact hright.not_ge hfirst

/-- The selected values eventually reach `⊥`. -/
private lemma subseqIdx_hits_bot (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ∃ N : ℕ, f (subseqIdx f atf hf N) = ⊥ :=
  ⟨atf.choose, le_bot_iff.mp <|
    le_of_le_of_eq (hf (subseqIdx.ge_self f atf hf atf.choose)) atf.choose_spec⟩

open Classical in
/-- The number of strict drops of the chain: the least index at which the selected values
reach `⊥`. -/
private noncomputable def subseqLen (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ℕ :=
  Nat.find (subseqIdx_hits_bot f atf hf)

open Classical in
private lemma subseqLen_spec (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    f (subseqIdx f atf hf (subseqLen f atf hf)) = ⊥ :=
  Nat.find_spec (subseqIdx_hits_bot f atf hf)

open Classical in
private lemma subseqIdx_ne_bot_of_lt (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    {i : ℕ} (hi : i < subseqLen f atf hf) : f (subseqIdx f atf hf i) ≠ ⊥ :=
  Nat.find_min (subseqIdx_hits_bot f atf hf) hi

open Classical in
/-- The selected values are strictly decreasing up to `subseqLen`. -/
private lemma subseqIdx_strictAnti (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ∀ i j : ℕ, i < j → j ≤ subseqLen f atf hf →
      f (subseqIdx f atf hf j) < f (subseqIdx f atf hf i) := by
  intro i j hij hj
  have hbot : f (subseqIdx f atf hf i) ≠ ⊥ :=
    subseqIdx_ne_bot_of_lt f atf hf (lt_of_lt_of_le hij hj)
  refine lt_of_le_of_lt
    (hf ((strictMono_nat_of_lt_succ (subseqIdx.lt_succ f atf hf)).monotone hij)) ?_
  rw [subseqIdx.succ_eq_find f atf hf i hbot]
  exact (Nat.find_spec (subseqIdx.next_exists f atf hf i hbot)).2

open Classical in
/-- If `f k = ⊥` and two consecutive values up to index `k` coincide, then the number of
strict drops differs from `k`. -/
private lemma subseqLen_ne_of_plateau (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    (k : ℕ) (hk : f k = ⊥) (htech : ∃ N : ℕ, N + 1 ≤ k ∧ f N = f (N + 1)) :
    subseqLen f atf hf ≠ k := by
  let A := subseqLen f atf hf
  let 𝒮 := {f t | (t ≤ k)}
  have helper : ∀ t : ℕ, ∃ l : ℕ, l ≤ k ∧ f (subseqIdx f atf hf t) = f l := by
    intro t
    if hcond : f (subseqIdx f atf hf t) = ⊥ then exact ⟨k, ⟨le_rfl, hcond ▸ hk.symm⟩⟩
    else
      refine ⟨subseqIdx f atf hf t, ?_, rfl⟩
      by_contra hlt
      exact hcond <| le_bot_iff.mp <| hk ▸ hf (lt_of_not_ge hlt).le
  let Φ : Fin (A + 1) → 𝒮 := fun d ↦
    let l := (helper d).choose
    let hl := (helper d).choose_spec
    ⟨f (subseqIdx f atf hf d), Set.mem_ofPred.mpr ⟨l, ⟨hl.1, hl.2.symm⟩⟩⟩
  have hΦ : Function.Injective Φ := by
    intro d1 d2 h
    have hvals : f (subseqIdx f atf hf d1) = f (subseqIdx f atf hf d2) :=
      congrArg Subtype.val h
    rcases lt_trichotomy d1 d2 with hlt | heq | hgt
    · exact False.elim ((subseqIdx_strictAnti f atf hf d1 d2 hlt (Fin.is_le d2)).ne hvals.symm)
    · exact heq
    · exact False.elim ((subseqIdx_strictAnti f atf hf d2 d1 hgt (Fin.is_le d1)).ne hvals)
  let fS : Fin (k + 1) → 𝒮 := fun m ↦ ⟨f m, Set.mem_ofPred.mpr ⟨m, ⟨Fin.is_le m, rfl⟩⟩⟩
  have fSsuj : Function.Surjective fS := by
    intro y
    rcases y.prop.out with ⟨n1, n2, n3⟩
    use ⟨n1, Nat.lt_succ_of_le n2⟩, SetCoe.ext n3
  have : Fintype 𝒮 := Set.Finite.fintype <| Finite.of_surjective fS fSsuj
  have ineq1 : A + 1 ≤ Fintype.card ↑𝒮 :=
    Fintype.card_fin (A + 1) ▸ Fintype.card_le_of_injective Φ hΦ
  have ineq2 : Fintype.card ↑𝒮 < k + 1 := Fintype.card_fin (k + 1) ▸
    Fintype.card_lt_of_surjective_not_injective fS fSsuj <| Function.not_injective_iff.mpr
    ⟨⟨htech.choose, Nat.lt_add_right 1 htech.choose_spec.1⟩, ⟨htech.choose + 1,
      Nat.add_lt_add_right htech.choose_spec.1 1⟩,
      ⟨SetCoe.ext htech.choose_spec.2, by simp⟩⟩
  exact ne_of_lt <| Nat.succ_lt_succ_iff.mp <| lt_of_le_of_lt ineq1 ineq2

open Classical in
/-- A predicate holding on the strict steps of `f` also holds on the steps of the chain
obtained by removing repeated values. -/
private lemma subseqIdx_inherit_step_predicate (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥)
    (hf : Antitone f) (P : StrictIntvl ℒ → Prop)
    (ho : ∀ i : ℕ, (hfi : f (i + 1) < f i) → P ⟨f (i + 1), f i, hfi⟩) :
    ∀ i : ℕ, (hi : i < subseqLen f atf hf) →
      P ⟨f (subseqIdx f atf hf (i + 1)), f (subseqIdx f atf hf i),
        subseqIdx_strictAnti f atf hf i (i + 1) (Nat.lt_succ_self i) hi⟩ := by
  intro i hi
  let n := subseqIdx f atf hf (i + 1)
  have hn : subseqIdx f atf hf i < n := subseqIdx.lt_succ f atf hf i
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hpred_eq : f (n - 1) = f (subseqIdx f atf hf i) := by
    apply subseqIdx.const_between f atf hf i (n - 1)
    repeat omega
  have hpred_lt : f ((n - 1) + 1) < f (n - 1) := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos), hpred_eq]
    exact subseqIdx_strictAnti f atf hf i (i + 1) (Nat.lt_succ_self i) hi
  convert ho (n - 1) hpred_lt using 1
  simp [n, hpred_eq, Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)]

end SubseqIdx

section NormalizeFiltration

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
variable [CompleteLattice S] {μ : PayoffFunction ℒ S}

/-- Remove the plateaus of an antitone chain whose strict steps satisfy the Jordan–Hölder
conditions. A plateau before the given bottom index makes the resulting filtration shorter. -/
private lemma exists_shorter_filtration_of_plateau (f : ℕ → ℒ) (k : ℕ)
    (hf : Antitone f) (hfirst : f 0 = ⊤) (hlast : f k = ⊥)
    (hpayoff : ∀ i, (hi : f (i + 1) < f i) → μ ⟨f (i + 1), f i, hi⟩ = μ ⊤)
    (hstable : ∀ i, (hi : f (i + 1) < f i) → ∀ z,
      (hz : f (i + 1) < z) → z < f i → μ ⟨f (i + 1), z, hz⟩ < μ ⟨f (i + 1), f i, hi⟩)
    (hplateau : ∃ i, i + 1 ≤ k ∧ f i = f (i + 1)) :
    ∃ F : μ.JordanHolderFiltration, F.length < k := by
  classical
  have reaches_bot : ∃ i, f i = ⊥ := ⟨k, hlast⟩
  let normalized : μ.JordanHolderFiltration :=
    { toFun := fun i ↦ f (subseqIdx f reaches_bot hf i)
      length := subseqLen f reaches_bot hf
      antitone := fun _ _ hij ↦
        hf ((strictMono_nat_of_lt_succ (subseqIdx.lt_succ f reaches_bot hf)).monotone hij)
      head_eq_top := hfirst
      length_eq_bot := subseqLen_spec f reaches_bot hf
      strictAntiOn := fun i _ j hj hij ↦ subseqIdx_strictAnti f reaches_bot hf i j hij hj
      step_payoff_eq := fun i hi ↦ subseqIdx_inherit_step_predicate f reaches_bot hf
        (fun I ↦ μ I = μ ⊤) hpayoff i hi
      payoff_lt_of_between := fun i hi z hz hz' ↦ subseqIdx_inherit_step_predicate f reaches_bot hf
        (fun I ↦ ∀ z, (hz : I.left < z) → z < I.right → μ ⟨I.left, z, hz⟩ < μ I)
        hstable i hi z hz hz' }
  refine ⟨normalized, ?_⟩
  apply lt_of_le_of_ne
  · -- The selected chain reaches bottom no later than the original bottom index.
    apply normalized.length_le_of_eq_bot
    exact le_bot_iff.mp (hlast ▸ hf (subseqIdx.ge_self f reaches_bot hf k))
  · -- A plateau means that at least one index has been removed.
    exact subseqLen_ne_of_plateau f reaches_bot hf k hlast hplateau

end NormalizeFiltration

/-! ### Length uniqueness -/

section RestrictLast

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- Restricting to the interval from the last nonbottom filtration term to `⊤` preserves
semistability. -/
private lemma isSemistable_restrict_last [μ.IsSlopeLike] [μ.IsSemistable]
    [μ.EventuallyTopDCC] (F : μ.JordanHolderFiltration) (h : F (F.length - 1) < ⊤) :
    (μ.restrict ⟨F (F.length - 1), ⊤, h⟩).IsSemistable := by
  apply isSemistable_of_hasNashEquilibrium (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
  apply min_top_eq_max_top_iff_hasNashEquilibrium.1
  apply min_top_eq_apply_iff.1
  rw [min_restrict_apply, restrict_apply, StrictIntvl.ofSub_top]
  apply eq_of_le_of_ge ?_ ?_
  · exact iInf₂_le (F (F.length - 1)) ⟨le_rfl, h⟩
  · refine le_iInf₂ fun u hu1 ↦ ?_
    have hmin : μ.min ⊤ = μ ⊤ :=
      min_top_eq_apply_iff.2 (min_top_eq_max_top_iff_hasNashEquilibrium.2
        (IsSemistable.hasNashEquilibrium inferInstance))
    calc
      μ ⟨F (F.length - 1), ⊤, h⟩ = μ ⊤ := by
        exact (((inferInstance : μ.IsSlopeLike).seesaw_total_eq_right_iff
          (F.bot_lt_of_lt (Nat.sub_one_lt F.length_pos.ne')) h).2
          (F.payoff_bot_eq_top_payoff (F.length - 1) (Nat.sub_one_lt F.length_pos.ne'))).symm
      _ = μ.min ⊤ := hmin.symm
      _ ≤ μ ⟨u, ⊤, hu1.2⟩ := iInf₂_le u ⟨bot_le, hu1.2⟩

end RestrictLast

section RestrictLastFiltration

variable {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
variable {S : Type*} [CompleteLattice S] {μ : PayoffFunction ℒ S}

/-- Removing the last step gives a filtration on the remaining top interval, with length
one less than the original, provided that interval has the original total payoff. -/
private lemma exists_filtration_restrict_last (F : μ.JordanHolderFiltration)
    (h : F (F.length - 1) < ⊤)
    (hpayoff : μ ⟨F (F.length - 1), ⊤, h⟩ = μ ⊤) :
    ∃ G : (μ.restrict ⟨F (F.length - 1), ⊤, h⟩).JordanHolderFiltration,
      G.length = F.length - 1 := by
  let interval : StrictIntvl ℒ := ⟨F (F.length - 1), ⊤, h⟩
  let truncated : ℕ → ↥interval := fun i ↦
    if hi : i ≤ F.length - 1 then ⟨F i, F.antitone hi, le_top⟩ else ⊥
  refine ⟨{
    toFun := truncated
    length := F.length - 1
    antitone := by
      intro i j hij
      by_cases hj : j ≤ F.length - 1
      · simp only [truncated, hij.trans hj, hj, ↓reduceDIte]
        exact F.antitone hij
      · simp only [truncated, hj, ↓reduceDIte, bot_le]
    head_eq_top := by
      apply Subtype.ext
      simp [truncated, interval]
    length_eq_bot := by
      simpa only [truncated, le_refl, ↓reduceDIte] using by rfl
    strictAntiOn := by
      intro i _ j hj hij
      rw [Set.mem_Iic] at hj
      simp only [truncated, hj, (hij.trans_le hj).le, ↓reduceDIte]
      exact F.apply_lt_apply hij (hj.trans (Nat.sub_le F.length 1))
    step_payoff_eq := by
      intro i hi
      have hsucc : i + 1 ≤ F.length - 1 := hi
      simp only [restrict_apply, truncated, hi.le, hsucc, ↓reduceDIte]
      exact (F.step_payoff (Nat.lt_of_lt_pred hi)).trans hpayoff.symm
    payoff_lt_of_between := by
      intro i hi z hz hz'
      have hsucc : i + 1 ≤ F.length - 1 := hi
      simp only [truncated, hsucc, hi.le, ↓reduceDIte] at hz hz'
      simp only [restrict_apply, truncated, hsucc, hi.le, ↓reduceDIte]
      exact F.payoff_lt (Nat.lt_of_lt_pred hi) hz hz' }, rfl⟩

end RestrictLastFiltration

section JoinedSteps

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [hsl : μ.IsSlopeLike] [hst : μ.IsSemistable] [μ.EventuallyTopDCC]

/-- The `μ.A`-value below any nonbottom filtration term is the total payoff. -/
private lemma A_bot_eq_top_payoff (F : μ.JordanHolderFiltration) (i : ℕ)
    (hi : i < F.length) : μ.A ⟨⊥, F i, F.bot_lt_of_lt hi⟩ = μ ⊤ := by
  have hpayoff := F.payoff_bot_eq_top_payoff i hi
  rw [← hsl.min_eq_A, ← hpayoff]
  refine le_antisymm min_le_apply (le_min fun u hu ↦ ?_)
  by_cases hu_bot : u = ⊥
  · simp only [hu_bot, le_refl]
  · by_contra! hsmaller
    have hgreater := (hsl.seesaw_right_lt_total_iff
      (bot_lt_iff_ne_bot.2 hu_bot) hu.2).1 hsmaller
    rw [hpayoff] at hgreater
    -- A smaller tail payoff would force an initial payoff above the semistable maximum.
    apply hgreater.not_ge
    calc
      μ ⟨⊥, u, bot_lt_iff_ne_bot.2 hu_bot⟩ ≤ μ.max ⊤ :=
        le_max (I := ⊤) ⟨bot_lt_iff_ne_bot.2 hu_bot, le_top⟩
      _ = μ ⊤ := max_top_eq_apply_iff.2
        (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)

/-- The interval from `⊥` to the join of a nonbottom filtration term with any term of
another filtration has the total payoff. -/
private lemma payoff_sup_eq_top_payoff [μ.IsConvex] (F G : μ.JordanHolderFiltration)
    (i : ℕ) (hi : i < F.length) (j : ℕ) :
    μ ⟨⊥, F i ⊔ G j, lt_of_lt_of_le (F.bot_lt_of_lt hi) le_sup_left⟩ = μ ⊤ := by
  apply le_antisymm
  · calc
      μ ⟨⊥, F i ⊔ G j, (F.bot_lt_of_lt hi).trans_le le_sup_left⟩ ≤ μ.max ⊤ :=
        le_max (I := ⊤) ⟨(F.bot_lt_of_lt hi).trans_le le_sup_left, le_top⟩
      _ = μ ⊤ := max_top_eq_apply_iff.2
        (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
  · refine le_trans ?_ (min_le_apply (μ := μ))
    rw [hsl.min_eq_A]
    by_cases hbot : G j = ⊥
    · simpa only [hbot, sup_bot_eq] using (A_bot_eq_top_payoff F i hi).ge
    · have hj : j < G.length := JordanHolderFiltration.ne_bot_iff_lt_length.1 hbot
      calc
        μ ⊤ = μ.A ⟨⊥, F i, F.bot_lt_of_lt hi⟩ ⊓ μ.A ⟨⊥, G j, G.bot_lt_of_lt hj⟩ := by
          rw [A_bot_eq_top_payoff F i hi, A_bot_eq_top_payoff G j hj, inf_idem]
        _ ≤ μ.A ⟨⊥, F i ⊔ G j, lt_sup_of_lt_left (F.bot_lt_of_lt hi)⟩ :=
          (inferInstance : μ.IsConvexOn ⊤).inf_A_le_A_sup
            (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _)
            (F.bot_lt_of_lt hi) (G.bot_lt_of_lt hj)

end JoinedSteps

section JoinedStability

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hmod : IsModularLattice ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [hsl : μ.IsSlopeLike] [haff : μ.IsAffine]

/-- Joining both endpoints of a step with a fixed element preserves the strict payoff
inequality, provided the joined step is strict and has the total payoff. -/
private lemma joined_step_stable (G : μ.JordanHolderFiltration) {x : ℒ} {j : ℕ}
    (hj : j < G.length) (hstep : x ⊔ G (j + 1) < x ⊔ G j)
    (hpayoff : μ ⟨x ⊔ G (j + 1), x ⊔ G j, hstep⟩ = μ ⊤)
    {w : ℒ} (hw₁ : x ⊔ G (j + 1) < w) (hw₂ : w < x ⊔ G j) :
    μ ⟨x ⊔ G (j + 1), w, hw₁⟩ < μ ⟨x ⊔ G (j + 1), x ⊔ G j, hstep⟩ := by
  have hxw : x ≤ w := le_sup_left.trans hw₁.le
  have hnot_le : ¬ G j ≤ w := fun hle ↦ hw₂.not_ge (sup_le hxw hle)
  -- The meet lies strictly inside the original step, where stability applies.
  have hmeet_lt : G (j + 1) < G j ⊓ w := by
    refine lt_of_le_of_ne
      (le_inf (G.antitone (Nat.le_succ j)) (le_sup_right.trans hw₁.le)) ?_
    intro heq
    have hmodular := hmod.sup_inf_le_assoc_of_le (G j) hxw
    rw [← heq, inf_eq_right.2 hw₂.le] at hmodular
    exact hw₁.not_ge hmodular
  -- Seesaw compares the upper pieces; affinity transports the meet payoff back to the join.
  apply (hsl.seesaw_total_lt_right_iff hw₁ hw₂).1
  calc
    μ ⟨x ⊔ G (j + 1), x ⊔ G j, hstep⟩ = μ ⊤ := hpayoff
    _ = μ ⟨G (j + 1), G j, G.apply_lt_apply (Nat.lt_succ_self j) hj⟩ :=
      (G.step_payoff hj).symm
    _ < μ ⟨G j ⊓ w, G j, inf_lt_left.2 hnot_le⟩ :=
      (hsl.seesaw_total_lt_right_iff hmeet_lt (inf_lt_left.2 hnot_le)).2
        (G.payoff_lt hj hmeet_lt (inf_lt_left.2 hnot_le))
    _ = μ ⟨w, x ⊔ G j, hw₂⟩ := by
      have hjoin : G j ⊔ w = x ⊔ G j :=
        le_antisymm (sup_le le_sup_right hw₂.le)
          (sup_le (hxw.trans le_sup_right) le_sup_left)
      simpa only [hjoin] using haff.eq (G j) w hnot_le

end JoinedStability

section JoinPlateau

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [hsl : μ.IsSlopeLike] [haff : μ.IsAffine]

/-- Joining every term of `G` with the last nonbottom term of `F` gives two equal consecutive
terms before `G` reaches `⊥`. -/
private lemma exists_join_plateau (F G : μ.JordanHolderFiltration) :
    ∃ i : ℕ, i + 1 ≤ G.length ∧
      F (F.length - 1) ⊔ G i = F (F.length - 1) ⊔ G (i + 1) := by
  classical
  let x := F (F.length - 1)
  have hlast : F.length - 1 < F.length := Nat.sub_one_lt F.length_pos.ne'
  -- Choose the last term of `G` containing `x`.
  let i := Nat.findGreatest (fun j ↦ x ≤ G j) (G.length - 1)
  have hi : i + 1 ≤ G.length :=
    (Nat.findGreatest_le (P := fun j ↦ x ≤ G j) _).trans_lt
      (Nat.sub_one_lt G.length_pos.ne')
  have hx_le : x ≤ G i :=
    Nat.findGreatest_spec (P := fun j ↦ x ≤ G j) (m := 0) (Nat.zero_le _)
      (by simp only [JordanHolderFiltration.apply_zero, le_top])
  have hx_not_le : ¬ x ≤ G (i + 1) := by
    by_cases hnext : i + 1 ≤ G.length - 1
    · exact Nat.findGreatest_is_greatest (lt_add_one _) hnext
    · have hnext_eq : i + 1 = G.length := by omega
      simpa only [hnext_eq, JordanHolderFiltration.apply_length, le_bot_iff] using
        F.ne_bot_of_lt hlast
  refine ⟨i, hi, ?_⟩
  rw [show x ⊔ G i = G i from sup_eq_right.mpr hx_le]
  symm
  apply eq_of_le_of_not_lt (sup_le hx_le (G.antitone (Nat.le_succ i)))
  intro hjoin_lt
  -- A strict joined step contradicts stability of `G`: affinity and stability of
  -- the last step of `F` give the reverse payoff inequality.
  have hnext_lt : G (i + 1) < x ⊔ G (i + 1) := right_lt_sup.mpr hx_not_le
  apply (G.payoff_lt hi hnext_lt hjoin_lt).not_ge
  calc
    μ ⟨G (i + 1), G i, G.apply_lt_apply (Nat.lt_succ_self i) hi⟩ = μ ⊤ :=
      G.step_payoff hi
    _ ≤ μ ⟨x ⊓ G (i + 1), x, inf_lt_left.mpr hx_not_le⟩ := by
      by_cases hmeet : x ⊓ G (i + 1) = ⊥
      · simpa only [hmeet] using (F.payoff_bot_eq_top_payoff _ hlast).ge
      · have hmeet_pos : ⊥ < x ⊓ G (i + 1) := bot_lt_iff_ne_bot.mpr hmeet
        rw [← F.payoff_bot_eq_top_payoff _ hlast]
        apply le_of_lt ((hsl.seesaw_total_lt_right_iff hmeet_pos
          (inf_lt_left.mpr hx_not_le)).2 ?_)
        simpa only [Nat.sub_one_add_one F.length_pos.ne',
          JordanHolderFiltration.apply_length] using F.payoff_lt hlast
            (by simpa only [Nat.sub_one_add_one F.length_pos.ne',
              JordanHolderFiltration.apply_length] using hmeet_pos) (inf_lt_left.mpr hx_not_le)
    _ = μ ⟨G (i + 1), x ⊔ G (i + 1), hnext_lt⟩ := haff.eq x (G (i + 1)) hx_not_le

end JoinPlateau

section JoinFiltration

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable [IsModularLattice ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [hsl : μ.IsSlopeLike] [μ.IsSemistable] [μ.EventuallyTopDCC] [μ.IsAffine]

/-- Joining `G` with the last nonbottom term of `F` and removing repeated values gives a
shorter filtration of the restricted payoff function. -/
private lemma exists_shorter_join_filtration (F G : μ.JordanHolderFiltration)
    (h : F (F.length - 1) < ⊤)
    (hpayoff : μ ⟨F (F.length - 1), ⊤, h⟩ = μ ⊤) :
    ∃ H : (μ.restrict ⟨F (F.length - 1), ⊤, h⟩).JordanHolderFiltration,
      H.length < G.length := by
  let x := F (F.length - 1)
  let I : StrictIntvl ℒ := ⟨x, ⊤, h⟩
  let joined : ℕ → ↥I := fun j ↦ ⟨x ⊔ G j, le_sup_left, le_top⟩
  have hlast : F.length - 1 < F.length := Nat.sub_one_lt F.length_pos.ne'
  have hx_pos : ⊥ < x := F.bot_lt_of_lt hlast
  have joined_payoff : ∀ j, (hj : joined (j + 1) < joined j) →
      μ ⟨x ⊔ G (j + 1), x ⊔ G j, hj⟩ = μ ⊤ := by
    intro j hj
    calc
      μ ⟨x ⊔ G (j + 1), x ⊔ G j, hj⟩ =
          μ ⟨⊥, x ⊔ G j, hx_pos.trans_le le_sup_left⟩ := by
        apply ((hsl.seesaw_total_eq_right_iff (hx_pos.trans_le le_sup_left) hj).2 ?_).symm
        rw [payoff_sup_eq_top_payoff F G _ hlast (j + 1),
          payoff_sup_eq_top_payoff F G _ hlast j]
      _ = μ ⊤ := payoff_sup_eq_top_payoff F G _ hlast j
  apply exists_shorter_filtration_of_plateau (μ := μ.restrict I) joined G.length
  case hf => exact fun _ _ hij ↦ sup_le_sup_left (G.antitone hij) x
  case hfirst => exact Subtype.ext (by simp [joined, I])
  case hlast => exact Subtype.ext (by simp [joined, I])
  case hpayoff => exact fun j hj ↦ (joined_payoff j hj).trans hpayoff.symm
  case hstable =>
    intro j hj w hw₁ hw₂
    have hj_length : j < G.length := by
      apply JordanHolderFiltration.ne_bot_iff_lt_length.1
      intro hbot
      apply hj.not_ge
      change x ⊔ G j ≤ x ⊔ G (j + 1)
      simp [hbot]
    exact joined_step_stable G hj_length hj (joined_payoff j hj) hw₁ hw₂
  case hplateau =>
    obtain ⟨j, hj, heq⟩ := exists_join_plateau F G
    exact ⟨j, hj, Subtype.ext heq⟩

end JoinFiltration

open Classical in
/-- If one Jordan–Hölder filtration has length at most `n`, then every Jordan–Hölder
filtration has length at most `n`. -/
private lemma length_le_of_exists_length_le (n : ℕ) :
    ∀ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
      [WellFoundedGT ℒ] [IsModularLattice ℒ]
      {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
      [μ.FiniteTotalPayoff] [μ.IsSlopeLike] [μ.IsSemistable]
      [μ.EventuallyTopDCC] [μ.IsAffine],
      (∃ F : μ.JordanHolderFiltration, F.length ≤ n) →
      ∀ G : μ.JordanHolderFiltration, G.length ≤ n := by
  induction n with
  | zero =>
    intro ℒ _ _ _ _ _ S _ μ _ _ _ _ _ ⟨F, hF⟩ _
    exact (F.length_pos.not_ge hF).elim
  | succ n ih =>
    intro ℒ _ _ _ _ _ S _ μ hfinite hsl _ _ _ ⟨F, hF⟩ G
    by_cases hlength : G.length = 1
    · omega
    have hlast_pos : 0 < G.length - 1 :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne G.length_pos (Ne.symm hlength))
    let I : StrictIntvl ℒ :=
      ⟨G (G.length - 1), ⊤, G.apply_lt_top hlast_pos (Nat.sub_le G.length 1)⟩
    have hlast : G.length - 1 < G.length := Nat.sub_one_lt G.length_pos.ne'
    have hpayoff : μ I = μ ⊤ := by
      symm
      apply (hsl.seesaw_total_eq_right_iff (G.bot_lt_of_lt hlast) I.lt).2
      exact G.payoff_bot_eq_top_payoff _ hlast
    -- The restricted payoff satisfies the hypotheses needed for induction.
    have hfinite_res : (μ.restrict I).FiniteTotalPayoff :=
      ⟨by simpa only [restrict_apply, StrictIntvl.ofSub_top, hpayoff] using hfinite.ne_top⟩
    have hsemistable_res : (μ.restrict I).IsSemistable := isSemistable_restrict_last G I.lt
    -- Joining shortens F, while removing the last step of G decreases its length by one.
    obtain ⟨shorter, hshorter⟩ := exists_shorter_join_filtration G F I.lt hpayoff
    obtain ⟨restricted, hrestricted⟩ := exists_filtration_restrict_last G I.lt hpayoff
    apply Nat.le_add_of_sub_le
    calc
      G.length - 1 = restricted.length := hrestricted.symm
      _ ≤ n := ih (μ := μ.restrict I)
        ⟨shorter, Nat.le_of_lt_succ (hshorter.trans_le hF)⟩ restricted

section LengthEq

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable [IsModularLattice ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [μ.FiniteTotalPayoff] [μ.IsSlopeLike] [μ.IsSemistable]
variable [μ.EventuallyTopDCC] [μ.IsAffine]

/-- Any two Jordan–Hölder filtrations of a semistable slope-like affine payoff function on a
modular lattice have the same length. -/
theorem JordanHolderFiltration.length_eq (F G : μ.JordanHolderFiltration) :
    F.length = G.length :=
  eq_of_le_of_ge
    (length_le_of_exists_length_le G.length ⟨G, le_rfl⟩ F)
    (length_le_of_exists_length_le F.length ⟨F, le_rfl⟩ G)

end LengthEq

end PayoffFunction

end HarderNarasimhan
