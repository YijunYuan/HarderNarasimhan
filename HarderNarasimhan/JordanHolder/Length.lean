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

This file proves that over a *modular* lattice, all Jordan–Hölder filtrations of an affine
payoff function have the same length (`JordanHolderFiltration.length_eq`).

The proof is by induction on the length: given a filtration `F` of length `≤ n + 1` and any
other filtration `G`, one restricts to the top interval `(G (G.length - 1), ⊤)`, pushes `F`
into it by joining with `G (G.length - 1)`, and normalises the resulting eventually-bottom
antitone chain to a strictly decreasing one.  Modularity and affinity make the normalised
chain a Jordan–Hölder filtration of the restricted payoff function of *strictly smaller*
length, which lets the induction hypothesis apply.

The normalisation machinery (`subseqIdx` and friends) is a general device for converting an
antitone chain `ℕ → ℒ` that eventually reaches `⊥` into the strictly decreasing chain of
its jump values; it is kept `private` to this file.

## Main results

* `JordanHolderFiltration.length_eq` : over a modular lattice, any two Jordan–Hölder
  filtrations of `μ` have the same length.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

/-! ### Normalising an eventually-bottom antitone chain

`subseqIdx f atf hf` greedily selects the indices at which the antitone chain `f` strictly
drops, producing a strictly decreasing subchain that reaches `⊥` after `subseqLen f atf hf`
steps.  All of this machinery is internal to the length-uniqueness proof. -/

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
/-- The greedy index sequence underlying the normalised subchain: if the currently selected
value is `⊥`, advance by one (to keep a genuine map `ℕ → ℕ`); otherwise jump to the first
later index where the value drops strictly. -/
private noncomputable def subseqIdx (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f) :
    ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      if hcond : f (subseqIdx f atf hf t) = ⊥ then subseqIdx f atf hf t + 1
      else Nat.find (exists_next_lt f atf hf (subseqIdx f atf hf t) hcond)

/-- The witness that, as long as the current selected value is not `⊥`, there is a later
index where `f` drops strictly. -/
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
/-- Between two consecutive selected indices, the chain is constant.  (The `Nat.find` calls
below need `Classical` decidability, as in the definition of `subseqIdx`.) -/
private lemma subseqIdx.const_between (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥) (hf : Antitone f)
    (i m : ℕ) (hleft : subseqIdx f atf hf i ≤ m) (hright : m < subseqIdx f atf hf (i + 1)) :
    f m = f (subseqIdx f atf hf i) := by
  by_cases hbot : f (subseqIdx f atf hf i) = ⊥
  · have hs : subseqIdx f atf hf (i + 1) = subseqIdx f atf hf i + 1 := by
      simp [subseqIdx, hbot]
    have hm : m = subseqIdx f atf hf i := by omega
    simp [hm]
  · have hs := subseqIdx.succ_eq_find f atf hf i hbot
    have hle : f m ≤ f (subseqIdx f atf hf i) := hf hleft
    apply eq_of_le_of_not_lt hle
    intro hlt
    by_cases hm : m = subseqIdx f atf hf i
    · simp [hm] at hlt
    · have hm' : subseqIdx f atf hf i < m := hleft.lt_of_ne fun hm' ↦ hm hm'.symm
      have hfind := Nat.find_min' (subseqIdx.next_exists f atf hf i hbot) ⟨hm', hlt⟩
      omega

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
/-- If the chain has a plateau strictly before it reaches `⊥` at index `k`, then the number
of strict drops is not `k`: there are strictly fewer distinct values than indices.  The
proof is a counting argument on the image set `{f t | t ≤ k}`. -/
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
    if hd : d1 < d2 then
      have hlt' := subseqIdx_strictAnti f atf hf d1 d2 hd (Fin.is_le d2)
      simp [hvals] at hlt'
    else
      if hd' : d2 < d1 then
        have hlt' := subseqIdx_strictAnti f atf hf d2 d1 hd' (Fin.is_le d1)
        simp [hvals] at hlt'
      else exact Fin.le_antisymm (le_of_not_gt hd') (le_of_not_gt hd)
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
/-- Transport a stepwise predicate from the strict steps of `f` to the strict steps of the
normalised subchain. -/
private lemma subseqIdx_inherit_step_predicate (f : ℕ → ℒ) (atf : ∃ k, f k = ⊥)
    (hf : Antitone f) (P : StrictIntvl ℒ → Prop)
    (ho : ∀ i : ℕ, (hfi : f (i + 1) < f i) → P ⟨f (i + 1), f i, hfi⟩) :
    ∀ i : ℕ, (hi : i < subseqLen f atf hf) →
      P ⟨f (subseqIdx f atf hf (i + 1)), f (subseqIdx f atf hf i),
        subseqIdx_strictAnti f atf hf i (i + 1) (Nat.lt_succ_self i) hi⟩ := by
  intro i hi
  have hbot : f (subseqIdx f atf hf i) ≠ ⊥ := subseqIdx_ne_bot_of_lt f atf hf hi
  let n := subseqIdx f atf hf (i + 1)
  have hn : subseqIdx f atf hf i < n := by
    dsimp only [n]
    rw [subseqIdx.succ_eq_find f atf hf i hbot]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hf i hbot)).1
  have hstep : f n < f (subseqIdx f atf hf i) := by
    dsimp only [n]
    rw [subseqIdx.succ_eq_find f atf hf i hbot]
    exact (Nat.find_spec (subseqIdx.next_exists f atf hf i hbot)).2
  have hpred_eq : f (n - 1) = f (subseqIdx f atf hf i) := by
    apply subseqIdx.const_between f atf hf i (n - 1)
    repeat omega
  have hpred_lt : f n < f (n - 1) := by rwa [hpred_eq]
  have hn_pos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ i) (subseqIdx.ge_self f atf hf (i + 1))
  have hpred_lt' : f ((n - 1) + 1) < f (n - 1) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)] using hpred_lt
  convert ho (n - 1) hpred_lt' using 1
  simp [n, hpred_eq, Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)]

end SubseqIdx

/-! ### Length uniqueness -/

section RestrictLast

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}

/-- The restriction of `μ` to the last-step top interval `(F (F.length - 1), ⊤)` of a
Jordan–Hölder filtration is semistable: its payoff on initial segments is pinned to the
total payoff by `payoff_bot_eq_top_payoff` and the seesaw property. -/
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
    have hge : μ ⟨u, ⊤, lt_top_iff_ne_top.2 hu1.2.ne⟩ ≥ μ ⊤ := by
      rw [← hmin]
      exact iInf₂_le u ⟨bot_le, hu1.2⟩
    have hbotF := F.payoff_bot_eq_top_payoff (F.length - 1) (Nat.sub_one_lt F.length_pos.ne')
    have hEq := ((inferInstance : μ.IsSlopeLike).seesaw_total_eq_right_iff
      (F.bot_lt_of_lt (Nat.sub_one_lt F.length_pos.ne')) h).2 hbotF
    rw [StrictIntvl.mk_bot_top] at hEq
    rwa [hEq] at hge

end RestrictLast

open Classical in
/-- The induction engine for length uniqueness: if some Jordan–Hölder filtration has length
`≤ n`, then every Jordan–Hölder filtration has length `≤ n`.  The lattice is quantified
inside the induction so that the induction hypothesis can be applied to the restriction of
`μ` to a top interval. -/
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
    exact absurd (nonpos_iff_eq_zero.mp hF) F.length_pos.ne'
  | succ n hn =>
    intro ℒ _ _ _ _ hmod S _ μ hftp hsl hst _ haff ⟨JHy, hJHy⟩ JHx
    let lenx := JHx.length
    let leny := JHy.length
    let x0 := JHx (lenx - 1)
    if htriv : lenx = 1 then exact htriv ▸ Nat.le_add_left 1 n
    else
    have hlenx_ne_zero : lenx ≠ 0 := JHx.length_pos.ne'
    have hlenx : 0 < lenx - 1 := by omega
    let Ires : StrictIntvl ℒ := ⟨x0, ⊤, JHx.apply_lt_top hlenx (Nat.sub_le lenx 1)⟩
    have hx0_bot : ⊥ < x0 := JHx.bot_lt_of_lt (Nat.sub_one_lt hlenx_ne_zero)
    have nt : x0 < ⊤ := JHx.apply_lt_top hlenx (Nat.sub_le lenx 1)
    have hlast_step := JHx.step_payoff (Nat.sub_one_lt hlenx_ne_zero)
    have hstepx0 : μ ⟨x0, ⊤, nt⟩ = μ ⊤ := by
      simp only [Nat.sub_one_add_one JHx.length_pos.ne',
        JordanHolderFiltration.apply_length] at hlast_step
      exact ((hsl.seesaw_total_eq_right_iff hx0_bot nt).2 hlast_step).symm
    have hftp_res : (μ.restrict Ires).FiniteTotalPayoff :=
      ⟨by simpa only [restrict_apply, StrictIntvl.ofSub_top] using
        hstepx0.symm ▸ hftp.ne_top⟩
    let JH_raw : ℕ → ↥Ires := fun m ↦ ⟨x0 ⊔ JHy m, le_sup_left, le_top⟩
    have JH_raw_antitone : Antitone JH_raw :=
      fun _ _ hab ↦ sup_le_sup_left (JHy.antitone hab) _
    have JH_raw_first_top : JH_raw 0 = ⊤ := by
      simpa only [JH_raw, JordanHolderFiltration.apply_zero, le_top, sup_of_le_right]
        using by rfl
    have hJHy_last : JHy leny = ⊥ := JHy.apply_length
    have JH_raw_fin_len : JH_raw leny = ⊥ := by
      simpa only [JH_raw, leny, hJHy_last, JordanHolderFiltration.apply_length, bot_le,
        sup_of_le_left] using by rfl
    have atRaw : ∃ k, JH_raw k = ⊥ := ⟨leny, JH_raw_fin_len⟩
    let JHfinal := fun m ↦ JH_raw (subseqIdx JH_raw atRaw JH_raw_antitone m)
    have JHfinal_first_top : JHfinal 0 = ⊤ := by
      simpa [JHfinal, subseqIdx] using JH_raw_first_top
    have hmax_top : μ.max ⊤ = μ ⊤ :=
      max_top_eq_apply_iff.2
        (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
    have hA_eq_tot : ∀ (F : μ.JordanHolderFiltration) (k : ℕ), (hk : k < F.length) →
        μ ⊤ = μ.A ⟨⊥, F k, F.bot_lt_of_lt hk⟩ := by
      intro F k hk
      rw [← hsl.min_eq_A]
      have hess := F.payoff_bot_eq_top_payoff k hk
      rw [← hess]
      refine eq_of_le_of_ge ?_ ?_
      · refine le_iInf₂ fun u hu1 ↦ ?_
        if hubot : u = ⊥ then simp only [hubot, le_refl]
        else
          by_contra! hc
          replace hc := (hsl.seesaw_right_lt_total_iff
            (bot_lt_iff_ne_bot.2 hubot) hu1.2).1 hc
          rw [hess] at hc
          have hμu : μ ⟨⊥, u, bot_lt_iff_ne_bot.mpr hubot⟩ ≤ μ ⊤ := by
            rw [← hmax_top]
            exact le_iSup₂_of_le u ⟨bot_lt_iff_ne_bot.2 hubot, le_top⟩ le_rfl
          exact not_le_of_gt hc hμu
      · exact min_le_apply
    have hjy_lt : ∀ j : ℕ, JH_raw (j + 1) < JH_raw j → j < leny := by
      intro j hfj
      by_contra hcontra
      have hjbot : JHy j = ⊥ :=
        le_bot_iff.mp (hJHy_last ▸ JHy.antitone (not_lt.1 hcontra))
      have hraw : JH_raw j = ⊥ := by
        have hval : x0 ⊔ JHy j = x0 := by rw [hjbot]; exact sup_bot_eq x0
        exact Subtype.ext hval
      exact not_lt_bot (hraw ▸ hfj)
    have hcond1 : ∀ j : ℕ, (hfj : JH_raw (j + 1) < JH_raw j) →
        (μ.restrict Ires) ⟨JH_raw (j + 1), JH_raw j, hfj⟩ = (μ.restrict Ires) ⊤ := by
      intro j hfj
      have hjy := hjy_lt j hfj
      simp only [restrict_apply, StrictIntvl.ofSub, JH_raw]
      have hj' : ∀ j : ℕ, j ≤ leny →
          μ ⟨⊥, x0 ⊔ JHy j, lt_of_lt_of_le hx0_bot le_sup_left⟩ = μ ⊤ := by
        refine fun j hj ↦ eq_of_le_of_ge ?_ ?_
        · rw [← hmax_top]
          exact le_iSup₂_of_le (x0 ⊔ JHy j)
            ⟨lt_of_lt_of_le hx0_bot le_sup_left, le_top⟩ le_rfl
        · refine le_trans ?_ (min_le_apply (μ := μ)
            (I := ⟨⊥, x0 ⊔ JHy j, lt_of_lt_of_le hx0_bot le_sup_left⟩))
          rw [hsl.min_eq_A ⟨⊥, x0 ⊔ JHy j, lt_of_lt_of_le hx0_bot le_sup_left⟩]
          if hjbot : ⊥ = JHy j then
            simp only [← hjbot, bot_le, sup_of_le_left]
            rw [← hsl.min_eq_A, ← JHx.step_payoff (Nat.sub_one_lt hlenx_ne_zero)]
            refine le_iInf₂ fun u hu1 ↦ ?_
            have hstep2 := JHx.payoff_lt_of_between (lenx - 1)
              (Nat.sub_one_lt hlenx_ne_zero) u
            simp only [JordanHolderFiltration.toFun_eq_coe, lenx,
              Nat.sub_one_add_one JHx.length_pos.ne',
              JordanHolderFiltration.apply_length] at *
            if ubot : u = ⊥ then simpa only [ubot] using le_rfl
            else
              replace hstep2 := hstep2 (bot_lt_iff_ne_bot.2 ubot) hu1.2
              exact le_of_lt <| (hsl.seesaw_total_lt_right_iff
                (bot_lt_iff_ne_bot.2 ubot) hu1.2).2 hstep2
          else
          have hsup : μ.A ⟨⊥, x0, hx0_bot⟩ ⊓ μ.A ⟨⊥, JHy j, Ne.bot_lt' hjbot⟩ ≤
              μ.A ⟨⊥, x0 ⊔ JHy j, lt_sup_of_lt_left hx0_bot⟩ :=
            (inferInstance : μ.IsConvexOn ⊤).inf_A_le_A_sup (StrictIntvl.mem_top _)
              (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hx0_bot (Ne.bot_lt' hjbot)
          convert hsup
          have t2 := hA_eq_tot JHy j <| by
            refine lt_of_le_of_ne hj ?_
            by_contra hc
            exact hjbot (hc ▸ JHy.apply_length).symm
          rw [← hA_eq_tot JHx (lenx - 1) (by omega), ← t2]
          exact (min_self (μ ⊤)).symm
      have tj1 := hj' j hjy.le
      have hkey := tj1 ▸ ((hsl.seesaw_total_eq_right_iff
        (lt_of_lt_of_le hx0_bot le_sup_left) hfj).2 <| tj1 ▸ hj' (j + 1) hjy)
      rw [← hkey]
      exact hstepx0.symm
    have hcond2 : ∀ j : ℕ, (hfj : JH_raw (j + 1) < JH_raw j) →
        ∀ w : ↥Ires, (hw : JH_raw (j + 1) < w) → w < JH_raw j →
          (μ.restrict Ires) ⟨JH_raw (j + 1), w, hw⟩ <
            (μ.restrict Ires) ⟨JH_raw (j + 1), JH_raw j, hfj⟩ := by
      intro j hfj w hw1 hw2
      have hjy := hjy_lt j hfj
      refine (hsl.seesaw_total_lt_right_iff
        (x := ↑(JH_raw (j + 1))) (y := ↑w) (z := ↑(JH_raw j)) hw1 hw2).1 ?_
      have hkey := hcond1 j hfj
      simp only [restrict_apply, StrictIntvl.ofSub] at hkey
      have hproblem : JHy (j + 1) ≠ JHy j ⊓ ↑w := by
        by_contra hc
        have hmodu := hmod.sup_inf_le_assoc_of_le (x := x0) (JHy j) (z := w.val)
          (le_of_lt <| lt_of_le_of_lt le_sup_left hw1)
        rw [← hc, inf_eq_right.2 (le_of_lt hw2 : (↑w : ℒ) ≤ x0 ⊔ JHy j)] at hmodu
        exact (not_le_of_gt hw1) hmodu
      have hnle : ¬ (JHy j ≤ ↑w) := by
        by_contra hc
        refine (not_le_of_gt hw2) <| sup_le_iff.2 ⟨?_, hc⟩
        exact le_of_lt <| lt_of_le_of_lt le_sup_left hw1
      have hx0w : x0 ≤ (↑w : ℒ) := le_of_lt (lt_of_le_of_lt le_sup_left hw1)
      have hval : (↑(JH_raw j) : ℒ) = JHy j ⊔ ↑w :=
        le_antisymm (sup_le (hx0w.trans le_sup_right) le_sup_left)
          (sup_le le_sup_right hw2.le)
      have heqs : μ ⟨↑w, ↑(JH_raw j), hw2⟩ =
          μ ⟨JHy j ⊓ ↑w, JHy j, inf_lt_left.2 hnle⟩ := by
        rw [haff.eq (JHy j) ↑w hnle]
        simp only [hval]
      rw [hkey]
      simp only [StrictIntvl.left_top, StrictIntvl.right_top]
      rw [heqs, ((by rfl) : μ ⟨↑(⊥ : ↥Ires), ↑(⊤ : ↥Ires), nt⟩ = μ ⟨x0, ⊤, nt⟩),
        hstepx0, ← JHy.step_payoff hjy]
      have hlt : JHy (j + 1) < JHy j ⊓ ↑w :=
        lt_of_le_of_ne (le_inf (JHy.antitone (Nat.le_add_right j 1))
          (le_of_lt (lt_of_le_of_lt le_sup_right hw1))) hproblem
      refine (hsl.seesaw_total_lt_right_iff hlt (inf_lt_left.2 hnle)).2 ?_
      exact JHy.payoff_lt hjy hlt (inf_lt_left.mpr hnle)
    let JH_FINAL : (μ.restrict Ires).JordanHolderFiltration :=
      { toFun := JHfinal
        length := subseqLen JH_raw atRaw JH_raw_antitone
        antitone := fun _ _ hij ↦ JH_raw_antitone <|
          (strictMono_nat_of_lt_succ (subseqIdx.lt_succ JH_raw atRaw JH_raw_antitone)).monotone
            hij
        head_eq_top := JHfinal_first_top
        length_eq_bot := subseqLen_spec JH_raw atRaw JH_raw_antitone
        strictAntiOn := fun i _ j hj hij ↦
          subseqIdx_strictAnti JH_raw atRaw JH_raw_antitone i j hij hj
        step_payoff_eq := fun i hi ↦
          subseqIdx_inherit_step_predicate JH_raw atRaw JH_raw_antitone
            (fun z ↦ (μ.restrict Ires) z = (μ.restrict Ires) ⊤) hcond1 i hi
        payoff_lt_of_between := fun i hi z h' h'' ↦
          subseqIdx_inherit_step_predicate JH_raw atRaw JH_raw_antitone
            (fun w ↦ ∀ z : ↥Ires, (hw : w.left < z) → z < w.right →
              (μ.restrict Ires) ⟨w.left, z, hw⟩ < (μ.restrict Ires) w)
            (fun j hfj w hw1 hw2 ↦ hcond2 j hfj w hw1 hw2) i hi z h' h'' }
    have ha : JH_FINAL.length < leny := by
      have hbot : JHfinal leny = ⊥ :=
        eq_bot_iff.2 <| JH_raw_fin_len ▸
          JH_raw_antitone (subseqIdx.ge_self JH_raw atRaw JH_raw_antitone leny)
      refine lt_of_le_of_ne (JH_FINAL.length_le_of_eq_bot hbot) ?_
      let i0 := Nat.findGreatest (fun m ↦ x0 ≤ JHy m) (leny - 1)
      refine subseqLen_ne_of_plateau JH_raw atRaw JH_raw_antitone leny JH_raw_fin_len
        ⟨i0, ⟨Nat.add_le_of_le_sub (Nat.one_le_iff_ne_zero.mpr JHy.length_pos.ne') <|
          Nat.findGreatest_le (leny - 1), ?_⟩⟩
      · have hspec0 := @Nat.findGreatest_spec 0 (fun m ↦ x0 ≤ JHy m)
          inferInstance (leny - 1) (Nat.zero_le _)
          (by simp only [JordanHolderFiltration.apply_zero, le_top])
        have hi0_last : ¬ i0 + 1 ≤ leny - 1 → i0 + 1 = leny := by
          intro hw
          refine le_antisymm ?_ <| le_of_not_gt fun hlt ↦ hw <|
            (Nat.le_sub_one_iff_lt JHy.length_pos).2 hlt
          exact Nat.add_le_of_le_sub (Nat.one_le_iff_ne_zero.mpr JHy.length_pos.ne') <|
            Nat.findGreatest_le (leny - 1)
        have hi0_imp : ¬ x0 ≤ JHy (i0 + 1) := by
          by_cases hw : i0 + 1 ≤ leny - 1
          · exact Nat.findGreatest_is_greatest (lt_add_one _) hw
          · simp only [hi0_last hw, leny, JordanHolderFiltration.apply_length, le_bot_iff]
            exact JHx.ne_bot_of_lt (Nat.sub_one_lt JHx.length_pos.ne')
        have h1 : (↑(JH_raw (i0 + 1)) : ℒ) = JHy i0 := by
          refine eq_of_le_of_not_lt
            (sup_le hspec0 <| JHy.antitone (Nat.le_add_right i0 1)) fun hc ↦ ?_
          have hi0_le : i0 ≤ leny - 1 := Nat.findGreatest_le (leny - 1)
          have hsmall : JHy (i0 + 1) < ↑(JH_raw (i0 + 1)) := by
            refine lt_of_le_of_ne le_sup_right ?_
            by_contra hcon
            if hw : i0 + 1 ≤ leny - 1 then
              exact @Nat.findGreatest_is_greatest (i0 + 1) (fun m ↦ x0 ≤ JHy m)
                inferInstance (leny - 1) (lt_add_one _) hw <| right_eq_sup.1 hcon
            else exact hi0_imp <| right_eq_sup.1 hcon
          have otherwise := JHy.payoff_lt ((Nat.le_sub_one_iff_lt JHy.length_pos).1 hi0_le)
            hsmall hc
          rw [JHy.step_payoff (lt_of_le_of_lt hi0_le (Nat.sub_one_lt JHy.length_pos.ne'))]
            at otherwise
          refine (lt_iff_not_ge.1 otherwise) ?_
          rw [← JHx.step_payoff (Nat.sub_one_lt JHx.length_pos.ne')]
          rw [(haff.eq x0 (JHy (i0 + 1)) hi0_imp).symm]
          if hif : JHx (JHx.length) = JHx (JHx.length - 1) ⊓ JHy (i0 + 1) then
            apply le_of_eq
            simp [lenx, x0, Nat.sub_one_add_one JHx.length_pos.ne', hif]
          else
            have hh : JHx (JHx.length) < JHx (JHx.length - 1) ⊓ JHy (i0 + 1) := by
              simp only [JordanHolderFiltration.apply_length] at hif
              simpa [JordanHolderFiltration.apply_length] using Ne.bot_lt' hif
            have hle2 := le_of_lt <| JHx.payoff_lt (Nat.sub_one_lt JHx.length_pos.ne')
              ((Nat.sub_one_add_one JHx.length_pos.ne') ▸ hh) (inf_lt_left.mpr hi0_imp)
            simp only [Nat.sub_one_add_one JHx.length_pos.ne'] at hle2
            exact byContradiction fun hcc ↦ (lt_iff_not_ge.1 <|
              (hsl.seesaw_right_lt_total_iff hh (inf_lt_left.mpr hi0_imp)).1 <|
                lt_of_not_ge (by
                  simpa only [Nat.sub_one_add_one JHx.length_pos.ne'] using hcc)) hle2
        exact Subtype.coe_inj.1 <| h1 ▸ (sup_eq_right.2 hspec0)
    let JHfun : ℕ → ↥Ires := fun m ↦
      if hm : m ≤ lenx - 1 then ⟨JHx m, JHx.antitone hm, le_top⟩ else ⊥
    have JHfun_antitone : Antitone JHfun := by
      intro n1 n2 hn12
      by_cases h3 : n2 ≤ lenx - 1
      · simp only [JHfun, le_trans hn12 h3, h3, ↓reduceDIte]
        exact JHx.antitone hn12
      · simp only [JHfun, h3, ↓reduceDIte, bot_le]
    let JHres : (μ.restrict Ires).JordanHolderFiltration :=
      { toFun := JHfun
        length := lenx - 1
        antitone := JHfun_antitone
        head_eq_top := by
          simpa only [JHfun, zero_le, ↓reduceDIte, JordanHolderFiltration.apply_zero]
            using by rfl
        length_eq_bot := by
          simp only [JHfun, le_refl, ↓reduceDIte]
          rfl
        strictAntiOn := by
          intro i _ j hj hij
          rw [Set.mem_Iic] at hj
          simp only [JHfun, hj, (hij.trans_le hj).le, ↓reduceDIte]
          exact Subtype.coe_lt_coe.1 (JHx.apply_lt_apply hij (hj.trans (Nat.sub_le lenx 1)))
        step_payoff_eq := by
          intro k1 hk1
          simp only [restrict_apply, JHfun]
          have hk1' : k1 + 1 ≤ lenx - 1 := hk1
          simp only [hk1.le, ↓reduceDIte, hk1']
          exact (JHx.step_payoff (Nat.lt_of_lt_pred hk1)).trans hstepx0.symm
        payoff_lt_of_between := by
          intro i hi z hz hz'
          have hi' : i + 1 ≤ lenx - 1 := hi
          have htemp : JHx (i + 1) < z.val := by
            simp only [JHfun, hi', ↓reduceDIte] at hz
            exact hz
          have htemp2 : z.val < JHx i := by
            simp only [JHfun, hi.le, ↓reduceDIte] at hz'
            exact hz'
          simp only [restrict_apply, JHfun]
          simp only [hi', ↓reduceDIte, hi.le, gt_iff_lt]
          exact JHx.payoff_lt (Nat.lt_of_lt_pred hi) htemp htemp2 }
    have hres_ss : (μ.restrict Ires).IsSemistable := isSemistable_restrict_last JHx nt
    exact Nat.le_add_of_sub_le (hn (μ := μ.restrict Ires)
      ⟨JH_FINAL, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ha hJHy)⟩ JHres)

section LengthEq

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
variable [IsModularLattice ℒ]
variable {S : Type*} [CompleteLinearOrder S] {μ : PayoffFunction ℒ S}
variable [μ.FiniteTotalPayoff] [μ.IsSlopeLike] [μ.IsSemistable]
variable [μ.EventuallyTopDCC] [μ.IsAffine]

/-- Over a modular lattice, any two Jordan–Hölder filtrations of an affine payoff function
have the same length.  This is the analogue for the Harder–Narasimhan Games of the classical
Jordan–Hölder uniqueness theorem. -/
theorem JordanHolderFiltration.length_eq (F G : μ.JordanHolderFiltration) :
    F.length = G.length :=
  eq_of_le_of_ge
    (length_le_of_exists_length_le G.length ⟨G, le_rfl⟩ F)
    (length_le_of_exists_length_le F.length ⟨F, le_rfl⟩ G)

end LengthEq

end PayoffFunction

end HarderNarasimhan
