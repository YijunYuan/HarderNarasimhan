/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.JordanHolder.Defs
public import Mathlib.Order.RelSeries

/-!
# Existence of Jordan–Hölder filtrations

A semistable slope-like payoff function with finite total payoff has a Jordan–Hölder
filtration if it satisfies the eventually-`⊤` descending chain condition, its codomain is a
complete linear order, and `>` is well-founded on the underlying nontrivial bounded lattice.

Starting from `⊤`, we choose a maximal point `p` strictly between `⊥` and the current term
such that the interval from `⊥` to `p` has payoff `μ ⊤`. If no such point exists, the next
term is `⊥`. Semistability, the seesaw property, and maximality give the required payoff
conditions on each step. The chain condition and finite total payoff ensure termination.
The maximal point need not be unique, so the construction can depend on the choices.

## Main results

* A `Nonempty` instance for `μ.JordanHolderFiltration`.
* `HarderNarasimhan.PayoffFunction.exists_relSeries_jordanHolderRel`: a finite series for
  `μ.jordanHolderRel` from `⊤` to `⊥`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [hacc : WellFoundedGT ℒ]
variable {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)

omit [CompleteLinearOrder S] in
open Classical in
/-- A chain starting at `⊤`, whose next term is a maximal point `p` strictly between `⊥` and
the current term such that the interval from `⊥` to `p` has total payoff, or `⊥` if none exists.

The choice uses well-foundedness of `>`: a minimal element for this relation is maximal in
the lattice order. -/
private noncomputable def JHFil (k : ℕ) : ℒ :=
  match k with
  | 0 => ⊤
  | n + 1 =>
    let 𝒮 := {p : ℒ | ∃ h : ⊥ < p, p < JHFil n ∧ μ ⟨⊥, p, h⟩ = μ ⊤}
    if h𝒮 : 𝒮.Nonempty then
      (hacc.wf.has_min 𝒮 h𝒮).choose
    else
      ⊥

omit [CompleteLinearOrder S] in
/-- Each term above `⊥` is strictly greater than its successor. -/
private lemma JHFil_anti_mono :
    ∀ k : ℕ, JHFil μ k > ⊥ → JHFil μ k > JHFil μ (k + 1) := by
  intro k hk
  simp only [JHFil]
  by_cases h : {p : ℒ | ∃ h : ⊥ < p, p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
  · simp only [h]
    exact (hacc.wf.has_min _ h).choose_spec.1.2.1
  · simpa only [h]

omit [CompleteLinearOrder S] in
/-- The chain `JHFil` is antitone: it decreases strictly until it reaches `⊥` and is
constantly `⊥` afterwards. -/
private lemma JHFil_antitone : Antitone (JHFil μ) :=
  antitone_nat_of_succ_le fun n ↦ by
    by_cases h : JHFil μ n = ⊥
    · refine le_of_eq_of_le ?_ bot_le
      have hempty : ¬ {p : ℒ | ∃ hp : ⊥ < p, p < JHFil μ n ∧ μ ⟨⊥, p, hp⟩ = μ ⊤}.Nonempty := by
        rintro ⟨p, -, hlt, -⟩
        exact not_lt_bot (h ▸ hlt)
      simpa only [JHFil] using dif_neg hempty
    · exact (JHFil_anti_mono μ n <| bot_lt_iff_ne_bot.2 h).le

variable [hsl : μ.IsSlopeLike]

open Classical in
/-- Each step of the chain before it reaches `⊥` has the total payoff. -/
private lemma JHFil_step_payoff_eq_tot :
    ∀ k : ℕ, (hk : JHFil μ k > ⊥) →
      μ ⟨JHFil μ (k + 1), JHFil μ k, JHFil_anti_mono μ k hk⟩ = μ ⊤ := by
  -- Every nonbottom term was chosen with total payoff (including the initial term).
  have payoff_from_bot : ∀ n : ℕ, (hn : ⊥ < JHFil μ n) →
      μ ⟨⊥, JHFil μ n, hn⟩ = μ ⊤ := by
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      by_cases hchoices : {p : ℒ | ∃ h : ⊥ < p,
          p < JHFil μ n ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
      · simpa only [JHFil, hchoices, ↓reduceDIte] using
          (hacc.wf.has_min _ hchoices).choose_spec.1.2.2
      · simp only [JHFil, hchoices, ↓reduceDIte, lt_self_iff_false] at hn
  intro k hk
  by_cases hbot : JHFil μ (k + 1) = ⊥
  · simpa only [hbot] using payoff_from_bot k hk
  · have hnext : ⊥ < JHFil μ (k + 1) := bot_lt_iff_ne_bot.2 hbot
    calc
      μ ⟨JHFil μ (k + 1), JHFil μ k, JHFil_anti_mono μ k hk⟩ =
          μ ⟨⊥, JHFil μ k, hk⟩ := by
        apply ((hsl.seesaw_total_eq_right_iff hnext (JHFil_anti_mono μ k hk)).2 ?_).symm
        rw [payoff_from_bot (k + 1) hnext, payoff_from_bot k hk]
      _ = μ ⊤ := payoff_from_bot k hk

variable [hftp : μ.FiniteTotalPayoff] [hdc : μ.EventuallyTopDCC]

/-- The chain reaches `⊥` in finitely many steps. -/
private lemma JHFil_fin_len : ∃ N : ℕ, JHFil μ N = ⊥ := by
  by_contra! hc
  rcases hdc.exists_eq_top (fun n ↦ JHFil μ n) (strictAnti_nat_of_succ_lt <|
    fun n ↦ JHFil_anti_mono μ n (bot_lt_iff_ne_bot.2 <| hc n)) with ⟨N, hN⟩
  exact hftp.ne_top.symm <| hN ▸
    JHFil_step_payoff_eq_tot μ N (bot_lt_iff_ne_bot.2 <| hc N)

open Classical in
/-- The least index at which `JHFil` reaches `⊥`. -/
private noncomputable def JHlen : ℕ := Nat.find (JHFil_fin_len μ)

open Classical in
private lemma JHFil_bot_lt {n : ℕ} (hn : n < JHlen μ) : ⊥ < JHFil μ n :=
  bot_lt_iff_ne_bot.2 (Nat.find_min (JHFil_fin_len μ) hn)

open Classical in
private lemma JHFil_length_eq_bot : JHFil μ (JHlen μ) = ⊥ := Nat.find_spec (JHFil_fin_len μ)

private lemma JHFil_strictAntiOn : StrictAntiOn (JHFil μ) (Set.Iic (JHlen μ)) :=
  fun x _ _y hy hxy ↦ lt_of_le_of_lt (JHFil_antitone μ hxy)
    (JHFil_anti_mono μ x (JHFil_bot_lt μ (lt_of_lt_of_le hxy hy)))

variable [hst : μ.IsSemistable]

omit hftp in
open Classical in
/-- Replacing the upper endpoint of a step by a strictly intermediate point strictly
decreases its payoff. -/
private lemma JHFil_refine_lt_step_payoff :
    ∀ k : ℕ, (hk : JHFil μ k > ⊥) → ∀ z : ℒ, (h' : JHFil μ (k + 1) < z) →
      (h'' : z < JHFil μ k) →
      μ ⟨JHFil μ (k + 1), z, h'⟩ <
        μ ⟨JHFil μ (k + 1), JHFil μ k, JHFil_anti_mono μ k hk⟩ := by
  intro k hk z h' h''
  have hzbot : ⊥ < z := lt_of_le_of_lt bot_le h'
  have hmax : μ.max ⊤ = μ ⊤ :=
    max_top_eq_apply_iff.2
      (min_top_eq_max_top_iff_hasNashEquilibrium.2 hst.hasNashEquilibrium)
  have hzle : μ ⟨⊥, z, hzbot⟩ ≤ μ ⊤ :=
    hmax ▸ le_iSup₂_of_le z ⟨hzbot, le_top⟩ le_rfl
  -- Equality would make z an admissible choice above the selected term.
  have hzlt : μ ⟨⊥, z, hzbot⟩ < μ ⊤ := by
    refine hzle.lt_of_ne fun heq ↦ ?_
    have hchoices : {p : ℒ | ∃ h : ⊥ < p,
        p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty :=
      ⟨z, hzbot, h'', heq⟩
    have hminimal := (hacc.wf.has_min _ hchoices).choose_spec.2 z ⟨hzbot, h'', heq⟩
    exact hminimal (by simpa only [JHFil, hchoices, ↓reduceDIte] using h')
  rw [JHFil_step_payoff_eq_tot μ k hk]
  by_cases hbot : JHFil μ (k + 1) = ⊥
  · simpa only [hbot] using hzlt
  · have hnext : ⊥ < JHFil μ (k + 1) := bot_lt_iff_ne_bot.2 hbot
    have hnext_payoff : μ ⟨⊥, JHFil μ (k + 1), hnext⟩ = μ ⊤ := by
      by_cases hchoices : {p : ℒ | ∃ h : ⊥ < p,
          p < JHFil μ k ∧ μ ⟨⊥, p, h⟩ = μ ⊤}.Nonempty
      · simpa only [JHFil, hchoices, ↓reduceDIte] using
          (hacc.wf.has_min _ hchoices).choose_spec.1.2.2
      · simp only [JHFil, hchoices, ↓reduceDIte, not_true_eq_false] at hbot
    calc
      μ ⟨JHFil μ (k + 1), z, h'⟩ < μ ⟨⊥, z, hzbot⟩ := by
        apply (hsl.seesaw_right_lt_total_iff hnext h').2
        rwa [hnext_payoff]
      _ < μ ⊤ := hzlt

/-- A semistable slope-like payoff function has a Jordan–Hölder filtration under the
finite total payoff and eventually-`⊤` descending chain hypotheses. -/
instance : Nonempty (μ.JordanHolderFiltration) :=
  ⟨{ toFun := JHFil μ
     length := JHlen μ
     antitone := JHFil_antitone μ
     head_eq_top := rfl
     length_eq_bot := JHFil_length_eq_bot μ
     strictAntiOn := JHFil_strictAntiOn μ
     step_payoff_eq := fun k hk ↦ JHFil_step_payoff_eq_tot μ k (JHFil_bot_lt μ hk)
     payoff_lt_of_between := fun i hi z h' h'' ↦
       JHFil_refine_lt_step_payoff μ i (JHFil_bot_lt μ hi) z h' h'' }⟩

/-- There is a finite series for `μ.jordanHolderRel` from `⊤` to `⊥`. -/
theorem exists_relSeries_jordanHolderRel :
    ∃ s : RelSeries (μ.jordanHolderRel), s.head = ⊤ ∧ s.last = ⊥ := by
  obtain ⟨F⟩ := (inferInstance : Nonempty (μ.JordanHolderFiltration))
  exact ⟨{ length := F.length
           toFun := fun n ↦ F (n : ℕ)
           step := fun n ↦ ⟨F.apply_lt_apply (Nat.lt_add_one (n : ℕ)) (Fin.is_le n.succ),
             F.step_payoff n.isLt, fun z h' h'' ↦ F.payoff_lt n.isLt h' h''⟩ },
    F.apply_zero, F.apply_length⟩

end PayoffFunction

end HarderNarasimhan
