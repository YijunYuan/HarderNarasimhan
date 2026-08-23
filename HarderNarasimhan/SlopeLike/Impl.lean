/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.SlopeLike.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto

/-!
This file contains implementation lemmas for the slope-like module.

It has two main roles:
1. Provide a more “case-split friendly” characterization of `SlopeLike μ` (`prop4d6`), turning the
  four conjunctive axioms into a disjunction of three mutually exclusive patterns (increasing,
  decreasing, constant).
2. Prove that the quotient construction `μQuotient r d` is slope-like under additivity hypotheses on
  `r` and `d` and a positivity condition when `r = 0`.

As an `Impl.lean` file, these lemmas are intended to support the public results in
`SlopeLike/Results.lean`.
-/

namespace HarderNarasimhan

namespace impl

/-
Internal namespace containing proof-engineering lemmas for `SlopeLike`.
-/

/--
Proposition 4.6 (implementation form): equivalence between `SlopeLike μ` and a tri-part “seesaw”
disjunction.

The right-hand side states that for any `x<y<z`, exactly one of the following patterns holds:
- strict increase: `μ(x,y) < μ(x,z) < μ(y,z)`,
- strict decrease: `μ(x,y) > μ(x,z) > μ(y,z)`, or
- constant: `μ(x,y) = μ(x,z) = μ(y,z)`.

API note: this form is often easier to use in proofs by cases, especially when `S` is (or behaves
like) a linear order.
-/
lemma prop4d6 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
SlopeLike μ ↔ ∀ (x y z : ℒ), (h : x < y ∧ y < z) → (
  μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩
) := by
  constructor
  · intro sl x y z h
    have sl := sl.slopelike x y z h
    by_cases h' : μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩
    · exact Or.inl ⟨h', Or.resolve_left sl.2.2.2 (not_le_of_gt h')⟩
    · by_cases h'' : μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(x, y), h.1⟩
      · exact Or.inr <| Or.inl ⟨h'', Or.resolve_left sl.1 (not_le_of_gt h'')⟩
      · have h₁ := not_lt_of_ge <| Or.resolve_left sl.2.1 h'
        exact Or.inr <| Or.inr ⟨(eq_of_le_of_not_lt (Or.resolve_right sl.2.2.2 h₁) h'').symm,
          eq_of_le_of_not_lt (Or.resolve_left sl.2.2.1 h'') h₁⟩
  · intro seesaw
    refine ⟨fun x y z h ↦ ?_⟩
    rcases seesaw x y z h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1.le, Or.inl h1, Or.inr h2.le, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inr h2.le, Or.inl h1, Or.inl h1.le⟩
    · exact ⟨Or.inl h1.le, Or.inr h2.ge, Or.inr h2.le, Or.inl h1.ge⟩


/--
In a nontrivial totally ordered real vector space, the principal cut of any vector is strictly
below `⊤` in the Dedekind–MacNeille completion.

This lemma is used to derive contradictions when an equality forces a principal cut to be `⊤`.
-/
lemma principal_lt_top
{V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Nontrivial V] :
∀ v : V, DedekindCut.principal v < (⊤ : DedekindCut V) := fun v ↦
  (exists_gt v).elim fun w hw ↦ DedekindCut.principal_lt_iff.2 ⟨w, trivial, hw⟩


/--
Helper lemma for `μQuotient`: when `r z > 0`, the value `μQuotient r d z` is represented by an
actual vector `μ : V`, and it satisfies `(r z) • μ = d z`.

API note: this provides a convenient witness for rewriting inequalities in the “positive rank” case.
-/
lemma μQuotient_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
[PosSMulStrictMono ℝ V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V) : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z > 0 →
  ∃ (μ : V), (μQuotient r d) z = DedekindCut.principal μ ∧ (r z) • μ = (d z) :=
  fun z h ↦ ⟨(r z)⁻¹ • d z, dif_pos h, smul_inv_smul₀ h.ne' (d z)⟩


/--
Proposition 4.8 (implementation form): `μQuotient r d` is slope-like.

Assumptions:
- Additivity of `d` and `r` along composable intervals: for `x<y<z`, we have
  `d(x,z) = d(x,y) + d(y,z)` and `r(x,z) = r(x,y) + r(y,z)`.
- Positivity condition: if `r(x,y) = 0` then `d(x,y) > 0`.

Conclusion:
- The quotient construction `μQuotient r d` satisfies the slope-like axiom.

API note: the proof proceeds by splitting on whether the relevant ranks are zero or positive, using
the Dedekind–MacNeille completion to model “infinite slope” as `⊤`.
-/
lemma prop4d8 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [AddCommGroup V] [Module ℝ V] [LinearOrder V] [IsOrderedAddMonoid V]
[PosSMulStrictMono ℝ V] [Nontrivial V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) → d ⟨(x, z), lt_trans h.1 h.2⟩ = d ⟨(x, y), h.1⟩ +
  d ⟨(y, z), h.2⟩ ∧ r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ + r ⟨(y, z), h.2⟩)
(h₂ : ∀ (x y : ℒ), (h : x < y) → r ⟨(x, y), h⟩ = 0 → d ⟨(x, y), h⟩ > 0)
: SlopeLike (μQuotient r d) := by
  refine (prop4d6 (μQuotient r d)).2 fun x y z h ↦ ?_
  obtain ⟨hd, hr⟩ := h₁ x y z h
  have etop : ∀ w : {p : ℒ × ℒ // p.1 < p.2}, r w = 0 → μQuotient r d w = ⊤ :=
    fun w hw ↦ dif_neg (by simp [hw])
  rcases eq_zero_or_pos (r ⟨(x, z), lt_trans h.1 h.2⟩) with h' | h'
  · -- all ranks vanish: all three slopes are `⊤`, the constant pattern
    obtain ⟨hxy, hyz⟩ := add_eq_zero.1 <| hr ▸ h'
    exact Or.inr <| Or.inr
      ⟨(etop _ hxy).trans (etop _ h').symm, (etop _ h').trans (etop _ hyz).symm⟩
  · obtain ⟨μxz, hxz₁, hxz₂⟩ := μQuotient_helper r d ⟨(x, z), lt_trans h.1 h.2⟩ h'
    have hlt : μQuotient r d ⟨(x, z), lt_trans h.1 h.2⟩ < ⊤ :=
      hxz₁ ▸ principal_lt_top μxz
    rcases eq_zero_or_pos (r ⟨(x, y), h.1⟩) with hxy | hxy
    · rcases eq_zero_or_pos (r ⟨(y, z), h.2⟩) with hyz | hyz
      · -- both short ranks zero would force `r (x,z) = 0`
        exact absurd (by rw [hr, hxy, hyz, add_zero]) h'.ne'
      · -- `r (x,y) = 0 < r (y,z)`: the strictly decreasing pattern
        refine Or.inr <| Or.inl ⟨hlt.trans_eq (etop _ hxy).symm, ?_⟩
        have h4 : r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(y, z), h.2⟩ := by rw [hr, hxy, zero_add]
        simp only [μQuotient, gt_iff_lt, h', hyz, ↓reduceDIte, DedekindCut.principal_lt_principal]
        exact h4 ▸ ((smul_lt_smul_iff_of_pos_left (inv_pos.2 h')).2 <|
          hd ▸ lt_add_of_pos_left (d ⟨(y, z), h.2⟩) <| h₂ x y h.1 hxy)
    · rcases eq_zero_or_pos (r ⟨(y, z), h.2⟩) with hyz | hyz
      · -- `r (y,z) = 0 < r (x,y)`: the strictly increasing pattern
        refine Or.inl ⟨?_, hlt.trans_eq (etop _ hyz).symm⟩
        have h4 : r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ := by rw [hr, hyz, add_zero]
        simp only [μQuotient, gt_iff_lt, h', hxy, ↓reduceDIte, DedekindCut.principal_lt_principal]
        exact h4 ▸ ((smul_lt_smul_iff_of_pos_left (inv_pos.2 h')).2 <|
          hd ▸ lt_add_of_pos_right (d ⟨(x, y), h.1⟩) <| h₂ y z h.2 hyz)
      · -- both short ranks positive: compare the underlying vectors directly
        obtain ⟨μxy, hxy₁, hxy₂⟩ := μQuotient_helper r d ⟨(x, y), h.1⟩ hxy
        obtain ⟨μyz, hyz₁, hyz₂⟩ := μQuotient_helper r d ⟨(y, z), h.2⟩ hyz
        have key : r ⟨(x, y), h.1⟩ • μxz + r ⟨(y, z), h.2⟩ • μxz =
            r ⟨(x, y), h.1⟩ • μxy + r ⟨(y, z), h.2⟩ • μyz := by
          rw [hxy₂, hyz₂, ← add_smul, ← hr, hxz₂, hd]
        simp only [hxy₁, hxz₁, hyz₁, gt_iff_lt, DedekindCut.principal_lt_principal,
          DedekindCut.principal_inj]
        by_cases hs : μxy < μxz
        · exact Or.inl ⟨hs, (smul_lt_smul_iff_of_pos_left hyz).1 <|
            (add_lt_add_iff_left <| r ⟨(x, y), h.1⟩ • μxy).1 <| lt_sub_iff_add_lt.1 <|
            (eq_sub_of_add_eq key) ▸ (smul_lt_smul_iff_of_pos_left hxy).2 hs⟩
        · by_cases hs' : μxy = μxz
          · refine Or.inr <| Or.inr ⟨hs', ?_⟩
            rw [hs'] at key
            have h_eq := (add_right_inj _).mp key
            exact le_antisymm ((smul_le_smul_iff_of_pos_left hyz).1 h_eq.le)
              ((smul_le_smul_iff_of_pos_left hyz).1 h_eq.ge)
          · have hs' : μxz < μxy := (not_lt.1 hs).lt_of_ne (Ne.symm hs')
            exact Or.inr <| Or.inl ⟨hs', (smul_lt_smul_iff_of_pos_left hyz).1 <|
              (add_lt_add_iff_left <| r ⟨(x, y), h.1⟩ • μxy).1 <| sub_lt_iff_lt_add.1 <|
              (eq_sub_of_add_eq key) ▸ (smul_lt_smul_iff_of_pos_left hxy).2 hs'⟩
end impl

end HarderNarasimhan
