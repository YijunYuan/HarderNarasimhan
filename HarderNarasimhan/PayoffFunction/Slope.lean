/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.SlopeLike
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Completion

/-!
# Slopes as payoff functions

This file constructs the prototypical slope-like payoff function: the quotient
`PayoffFunction.slope r d` of a vector-valued *degree* `d` by a nonnegative real *rank* `r`,
with values in the Dedekind–MacNeille completion `DedekindCut V` so that intervals of rank
zero receive the “infinite slope” `⊤`.

## Main definitions

* `PayoffFunction.slope r d` : the payoff `(r I)⁻¹ • d I` when `r I > 0`, and `⊤` otherwise.

## Main results

* `PayoffFunction.isSlopeLike_slope` : if `d` and `r` are additive on composable intervals
  and `d` is positive on rank-zero intervals, then `slope r d` is slope-like.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

open scoped NNReal

namespace HarderNarasimhan

/-- In a nontrivial linearly ordered additive group, the principal cut of any element is
strictly below `⊤` in the Dedekind–MacNeille completion. -/
lemma _root_.DedekindCut.principal_lt_top
    {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Nontrivial V] (v : V) :
    DedekindCut.principal v < (⊤ : DedekindCut V) :=
  (exists_gt v).elim fun w hw ↦ DedekindCut.principal_lt_iff.2 ⟨w, trivial, hw⟩

namespace PayoffFunction

variable {ℒ : Type*} [PartialOrder ℒ]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
  [PosSMulStrictMono ℝ V]

/-- The *slope* payoff function of a nonnegative real-valued rank `r` and a vector-valued
degree `d`: an interval `I` with `r I > 0` receives the quotient `(r I)⁻¹ • d I` as a
principal cut in the Dedekind–MacNeille completion, and an interval of rank zero receives
`⊤` (“infinite slope”). -/
noncomputable def slope (r : StrictIntvl ℒ → ℝ≥0) (d : StrictIntvl ℒ → V) :
    PayoffFunction ℒ (DedekindCut V) :=
  ⟨fun I ↦ if _ : 0 < r I then .principal ((r I)⁻¹ • d I) else ⊤⟩

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℝ V] in
/-- On an interval of positive rank, `slope r d` is the principal cut of a vector `v` with
`r I • v = d I`. -/
private lemma slope_pos {r : StrictIntvl ℒ → ℝ≥0} {d : StrictIntvl ℒ → V}
    {I : StrictIntvl ℒ} (h : 0 < r I) :
    ∃ v : V, slope r d I = DedekindCut.principal v ∧ r I • v = d I :=
  ⟨(r I)⁻¹ • d I, dif_pos h, smul_inv_smul₀ h.ne' (d I)⟩

/-- The slope of an additive degree by an additive rank is slope-like, provided the degree
is positive on intervals of rank zero. -/
theorem isSlopeLike_slope [Nontrivial V] (r : StrictIntvl ℒ → ℝ≥0) (d : StrictIntvl ℒ → V)
    (hd : ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      d ⟨x, z, h₁.trans h₂⟩ = d ⟨x, y, h₁⟩ + d ⟨y, z, h₂⟩)
    (hr : ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      r ⟨x, z, h₁.trans h₂⟩ = r ⟨x, y, h₁⟩ + r ⟨y, z, h₂⟩)
    (hpos : ∀ (x y : ℒ), (h : x < y) → r ⟨x, y, h⟩ = 0 → 0 < d ⟨x, y, h⟩) :
    (slope r d).IsSlopeLike := by
  refine isSlopeLike_iff_seesaw.2 fun x y z h₁ h₂ ↦ ?_
  have hdegree := hd x y z h₁ h₂
  have hrank := hr x y z h₁ h₂
  have etop : ∀ w : StrictIntvl ℒ, r w = 0 → slope r d w = ⊤ :=
    fun w hw ↦ dif_neg (by simp [hw])
  rcases eq_zero_or_pos (r ⟨x, z, h₁.trans h₂⟩) with htotal | htotal
  · -- all ranks vanish: all three slopes are `⊤`, the constant pattern
    obtain ⟨hxy, hyz⟩ := add_eq_zero.1 <| hrank ▸ htotal
    exact Or.inr <| Or.inr
      ⟨(etop _ hxy).trans (etop _ htotal).symm, (etop _ htotal).trans (etop _ hyz).symm⟩
  · obtain ⟨μxz, hxz₁, hxz₂⟩ := slope_pos (d := d) htotal
    have hlt : slope r d ⟨x, z, h₁.trans h₂⟩ < ⊤ := hxz₁ ▸ DedekindCut.principal_lt_top μxz
    rcases eq_zero_or_pos (r ⟨x, y, h₁⟩) with hxy | hxy
    · rcases eq_zero_or_pos (r ⟨y, z, h₂⟩) with hyz | hyz
      · -- both short ranks zero would force `r (x, z) = 0`
        exact absurd (by rw [hrank, hxy, hyz, add_zero]) htotal.ne'
      · -- `r (x, y) = 0 < r (y, z)`: the strictly decreasing pattern
        refine Or.inr <| Or.inl ⟨hlt.trans_eq (etop _ hxy).symm, ?_⟩
        have hsame_rank : r ⟨x, z, h₁.trans h₂⟩ = r ⟨y, z, h₂⟩ := by rw [hrank, hxy, zero_add]
        simp only [slope, coe_mk, htotal, hyz, ↓reduceDIte, DedekindCut.principal_lt_principal]
        exact hsame_rank ▸ ((smul_lt_smul_iff_of_pos_left (inv_pos.2 htotal)).2 <|
          hdegree ▸ lt_add_of_pos_left (d ⟨y, z, h₂⟩) <| hpos x y h₁ hxy)
    · rcases eq_zero_or_pos (r ⟨y, z, h₂⟩) with hyz | hyz
      · -- `r (y, z) = 0 < r (x, y)`: the strictly increasing pattern
        refine Or.inl ⟨?_, hlt.trans_eq (etop _ hyz).symm⟩
        have hsame_rank : r ⟨x, z, h₁.trans h₂⟩ = r ⟨x, y, h₁⟩ := by rw [hrank, hyz, add_zero]
        simp only [slope, coe_mk, htotal, hxy, ↓reduceDIte, DedekindCut.principal_lt_principal]
        exact hsame_rank ▸ ((smul_lt_smul_iff_of_pos_left (inv_pos.2 htotal)).2 <|
          hdegree ▸ lt_add_of_pos_right (d ⟨x, y, h₁⟩) <| hpos y z h₂ hyz)
      · -- both short ranks positive: compare the underlying vectors directly
        obtain ⟨μxy, hxy₁, hxy₂⟩ := slope_pos (d := d) hxy
        obtain ⟨μyz, hyz₁, hyz₂⟩ := slope_pos (d := d) hyz
        have hweighted : r ⟨x, y, h₁⟩ • μxz + r ⟨y, z, h₂⟩ • μxz =
            r ⟨x, y, h₁⟩ • μxy + r ⟨y, z, h₂⟩ • μyz := by
          rw [hxy₂, hyz₂, ← add_smul, ← hrank, hxz₂, hdegree]
        simp only [hxy₁, hxz₁, hyz₁, DedekindCut.principal_lt_principal,
          DedekindCut.principal_inj]
        rcases lt_trichotomy μxy μxz with hlt | heq | hgt
        · refine Or.inl ⟨hlt, ?_⟩
          apply (smul_lt_smul_iff_of_pos_left hyz).1
          apply (add_lt_add_iff_left (r ⟨x, y, h₁⟩ • μxy)).1
          calc
            r ⟨x, y, h₁⟩ • μxy + r ⟨y, z, h₂⟩ • μxz <
                r ⟨x, y, h₁⟩ • μxz + r ⟨y, z, h₂⟩ • μxz :=
              add_lt_add_of_lt_of_le ((smul_lt_smul_iff_of_pos_left hxy).2 hlt) le_rfl
            _ = r ⟨x, y, h₁⟩ • μxy + r ⟨y, z, h₂⟩ • μyz := hweighted
        · refine Or.inr (Or.inr ⟨heq, ?_⟩)
          rw [heq] at hweighted
          have hright := (add_right_inj _).mp hweighted
          exact le_antisymm ((smul_le_smul_iff_of_pos_left hyz).1 hright.le)
            ((smul_le_smul_iff_of_pos_left hyz).1 hright.ge)
        · refine Or.inr (Or.inl ⟨hgt, ?_⟩)
          apply (smul_lt_smul_iff_of_pos_left hyz).1
          apply (add_lt_add_iff_left (r ⟨x, y, h₁⟩ • μxy)).1
          calc
            r ⟨x, y, h₁⟩ • μxy + r ⟨y, z, h₂⟩ • μyz =
                r ⟨x, y, h₁⟩ • μxz + r ⟨y, z, h₂⟩ • μxz := hweighted.symm
            _ < r ⟨x, y, h₁⟩ • μxy + r ⟨y, z, h₂⟩ • μxz :=
              add_lt_add_of_lt_of_le ((smul_lt_smul_iff_of_pos_left hxy).2 hgt) le_rfl

end PayoffFunction

end HarderNarasimhan
