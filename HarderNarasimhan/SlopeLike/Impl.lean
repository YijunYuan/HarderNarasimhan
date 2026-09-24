/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.SlopeLike.Defs
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Tauto

/-!
# Section 4.3: slope-like payoff functions — proofs

Proofs of Propositions 4.6 and 4.8 and the comparison API derived from the seesaw property.
-/

@[expose] public section

open scoped NNReal

namespace HarderNarasimhan.Impl

open _root_.HarderNarasimhan.PayoffFunction

namespace PayoffFunction

variable {ℒ S : Type*} [PartialOrder ℒ] [CompleteLattice S]

variable {μ : PayoffFunction ℒ S}

/-- Definition 4.5 (restriction property). Slope-likeness is stable under restriction to a
subinterval. -/
instance {I : StrictIntvl ℒ} [hsl : μ.IsSlopeLike] : (μ.restrict I).IsSlopeLike :=
  ⟨fun x y z h ↦ hsl.slopelike x.val y.val z.val h⟩

/-- Proposition 4.6. The slope-like axiom is equivalent to the seesaw trichotomy: for any chain `x
< y < z` the three values `μ (x, y)`, `μ (x, z)`, `μ (y, z)` are strictly increasing, strictly
decreasing, or all equal. -/
theorem isSlopeLike_iff_seesaw :
    μ.IsSlopeLike ↔ ∀ (x y z : ℒ), (h₁ : x < y) → (h₂ : y < z) →
      (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
      (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
      (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) := by
  constructor
  · intro sl x y z h₁ h₂
    have sl := sl.slopelike x y z ⟨h₁, h₂⟩
    by_cases h' : μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩
    · exact Or.inl ⟨h', sl.2.2.2.resolve_left (not_le_of_gt h')⟩
    · by_cases h'' : μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩
      · exact Or.inr <| Or.inl ⟨h'', sl.1.resolve_left (not_le_of_gt h'')⟩
      · have h₃ := not_lt_of_ge <| sl.2.1.resolve_left h'
        exact Or.inr <| Or.inr ⟨(eq_of_le_of_not_lt (sl.2.2.2.resolve_right h₃) h'').symm,
          eq_of_le_of_not_lt (sl.2.2.1.resolve_left h'') h₃⟩
  · intro seesaw
    refine ⟨fun x y z h ↦ ?_⟩
    rcases seesaw x y z h.1 h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1.le, Or.inl h1, Or.inr h2.le, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inr h2.le, Or.inl h1, Or.inl h1.le⟩
    · exact ⟨Or.inl h1.le, Or.inr h2.ge, Or.inr h2.le, Or.inl h1.ge⟩

/-- Proposition 4.6 (forward implication). The seesaw trichotomy for a slope-like payoff function:
the three values `μ (x, y)`, `μ (x, z)`, `μ (y, z)` are strictly increasing, strictly
decreasing, or all equal. -/
lemma IsSlopeLike.seesaw (hsl : μ.IsSlopeLike) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z) :
    (μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩) ∨
    (μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ ∧ μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩) ∨
    (μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ ∧ μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩) :=
  isSlopeLike_iff_seesaw.1 hsl x y z h₁ h₂

section Seesaw

variable (hsl : μ.IsSlopeLike) {x y z : ℒ} (h₁ : x < y) (h₂ : y < z)
include hsl

/-- Auxiliary comparison for Proposition 4.6. The total payoff is less than the right payoff iff
the left payoff is less than the total payoff. -/
lemma IsSlopeLike.seesaw_total_lt_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true hb ha
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_false hb.not_lt ha.not_lt

/-- Auxiliary comparison for Proposition 4.6. The left payoff is less than the right payoff iff it
is less than the total payoff. -/
lemma IsSlopeLike.seesaw_left_lt_right_iff :
    μ ⟨x, y, h₁⟩ < μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ < μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_true (ha.trans hb) ha
  · exact iff_of_false (asymm (hb.trans ha)) (asymm ha)
  · exact iff_of_false (ha.trans hb).not_lt ha.not_lt

/-- Auxiliary comparison for Proposition 4.6. The right payoff is less than the total payoff iff
the total payoff is less than the left payoff. -/
lemma IsSlopeLike.seesaw_right_lt_total_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, z, h₁.trans h₂⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm hb) (asymm ha)
  · exact iff_of_true hb ha
  · exact iff_of_false hb.not_gt ha.not_gt

/-- Auxiliary comparison for Proposition 4.6. The right payoff is less than the left payoff iff
the total payoff is less than the left payoff. -/
lemma IsSlopeLike.seesaw_right_lt_left_iff :
    μ ⟨y, z, h₂⟩ < μ ⟨x, y, h₁⟩ ↔ μ ⟨x, z, h₁.trans h₂⟩ < μ ⟨x, y, h₁⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (asymm (ha.trans hb)) (asymm ha)
  · exact iff_of_true (hb.trans ha) ha
  · exact iff_of_false (ha.trans hb).not_gt ha.not_gt

/-- Auxiliary comparison for Proposition 4.6. The total and right payoffs are equal iff the left
and total payoffs are equal. -/
lemma IsSlopeLike.seesaw_total_eq_right_iff :
    μ ⟨x, z, h₁.trans h₂⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false hb.ne ha.ne
  · exact iff_of_false hb.ne' ha.ne'
  · exact iff_of_true hb ha

/-- Auxiliary comparison for Proposition 4.6. The left and right payoffs are equal iff the left
and total payoffs are equal. -/
lemma IsSlopeLike.seesaw_left_eq_right_iff :
    μ ⟨x, y, h₁⟩ = μ ⟨y, z, h₂⟩ ↔ μ ⟨x, y, h₁⟩ = μ ⟨x, z, h₁.trans h₂⟩ := by
  rcases IsSlopeLike.seesaw hsl h₁ h₂ with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact iff_of_false (ha.trans hb).ne ha.ne
  · exact iff_of_false (hb.trans ha).ne' ha.ne'
  · exact iff_of_true (ha.trans hb) ha

end Seesaw

end PayoffFunction

/-- Auxiliary completion lemma for Proposition 4.8. In a nontrivial linearly ordered additive
group, the principal cut of any element is strictly below `⊤` in the Dedekind–MacNeille
completion. -/
lemma DedekindCut.principal_lt_top
    {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Nontrivial V] (v : V) :
    DedekindCut.principal v < (⊤ : DedekindCut V) :=
  (exists_gt v).elim fun w hw ↦ DedekindCut.principal_lt_iff.2 ⟨w, trivial, hw⟩

namespace PayoffFunction

variable {ℒ : Type*} [PartialOrder ℒ]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
  [PosSMulStrictMono ℝ V]

omit [IsOrderedAddMonoid V] [PosSMulStrictMono ℝ V] in
/-- Auxiliary positive-rank formula for Proposition 4.8. On an interval of positive rank, `slope r
d` is the principal cut of a vector `v` with `r I • v = d I`. -/
private lemma slope_pos {r : StrictIntvl ℒ → ℝ≥0} {d : StrictIntvl ℒ → V}
    {I : StrictIntvl ℒ} (h : 0 < r I) :
    ∃ v : V, slope r d I = DedekindCut.principal v ∧ r I • v = d I :=
  ⟨(r I)⁻¹ • d I, dif_pos h, smul_inv_smul₀ h.ne' (d I)⟩

/-- Proposition 4.8. The slope of an additive degree by an additive rank is slope-like, provided
the degree is positive on intervals of rank zero. -/
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
        simp only [hxy₁, hxz₁, hyz₁, DedekindCut.principal_lt_principal, DedekindCut.principal_inj]
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

end HarderNarasimhan.Impl
