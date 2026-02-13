import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Defs
import Mathlib.Tactic

/-!
This file contains implementation lemmas for the convexity module.

As the name `Impl.lean` suggests, the statements here are primarily proof-engineering tools:
- equivalences between global and interval-local convexity,
- compatibility of convexity with restriction (`Resμ`) and with derived constructions such as `μmax`
  and `μA`,
- the technical inequalities and case splits used to derive the “paper-facing” results in
  `HarderNarasimhan.Convexity.Results`.

Most users should import `HarderNarasimhan.Convexity.Results` instead of relying on these lemmas
directly.
-/
namespace HarderNarasimhan

namespace impl

/-
Internal namespace for proof steps that back the public convexity results.

API note: names here often mirror lemma/proposition numbers from the accompanying paper, and are not
intended to be stable user-facing identifiers.
-/

/-
Convexity on the total interval is equivalent to global convexity.

This lemma bridges the localized class `ConvexI TotIntvl μ` and the global class `Convex μ`.
It is marked `[simp]` so that typeclass conversions can be reduced automatically.
-/
@[simp]
lemma ConvexI_TotIntvl_iff_Convex {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : ConvexI TotIntvl μ ↔
Convex μ := by
  constructor
  · intro h
    refine {convex := ?_ }
    exact fun x y hxy ↦ h.convex x y (in_TotIntvl _) (in_TotIntvl _) hxy
  · intro h
    refine { convex := ?_ }
    exact fun x y a a h_4 ↦ Convex.convex x y h_4

/-
Interval-local convexity is equivalent to global convexity of the restricted measure `Resμ I μ`.

Mathematically: convexity on an interval `I` for `μ` is the same as convexity on the total interval
for the induced function on `Interval I`.

API note: this is a key adapter used whenever we pass between “ambient” and “interval subtype”
viewpoints.
-/
lemma ConvexI_iff_Convex_Res {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(I : {p :ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : ConvexI I μ ↔ Convex (Resμ I μ) := by
  constructor
  · intro h
    refine {convex := ?_ }
    intro x y hxy
    unfold Resμ
    simp only
    exact h.convex x.val y.val x.prop y.prop hxy
  · intro h
    refine {convex := ?_ }
    intro x y hxI hyI hxy
    exact h.convex ⟨x,hxI⟩ ⟨y,hyI⟩ hxy

/-
Typeclass instance: a globally convex `μ` induces interval-local convexity on the total interval.

This is a convenience instance so that `Convex μ` can be used wherever `ConvexI TotIntvl μ` is
expected.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} [Convex μ] :
ConvexI TotIntvl μ := by
  simp only [ConvexI_TotIntvl_iff_Convex]
  infer_instance

/-
Typeclass instance: interval-local convexity on the total interval implies global convexity.

This is the reverse direction of the previous instance.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} [ConvexI TotIntvl μ] :
Convex μ := by
  simp only [← ConvexI_TotIntvl_iff_Convex]
  infer_instance


section

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
variable {S : Type*} [CompleteLattice S]

/-
Paper Lemma 2.4 (part 1) in interval form: a basic bound comparing `μA` to `μmax`.

This lemma is used as the leftmost inequality in the main inequality chain of Lemma 2.4.
It is written in a general lattice/complete lattice setting, and is later specialized to the total
interval.
-/
lemma lem2d4₁
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (w : ℒ) (hxw : ¬ x ≤ w)
  (u : ℒ) (huxw : u ≤ x ⊓ w) :
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩
    ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
  have h1 : μA μ ⟨(u, x), lt_of_le_of_lt huxw
    (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
    refine sInf_le_sInf fun t ht ↦ ?_
    rcases ht with ⟨a, ha, _⟩
    use a, ⟨⟨le_trans huxw ha.1.1, ha.1.2⟩, ha.2⟩
  have h2 : μA μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ := by
    apply sInf_le
    use x ⊓ w, ⟨⟨le_rfl, le_of_lt <| inf_lt_left.2 hxw⟩, ne_of_lt <| inf_lt_left.2 hxw⟩
  exact le_trans h1 h2


/-
Paper Lemma 2.4 (part 2) localized to an interval `I`.

Assuming convexity of `μ` on `I`, this gives a bound between two `μmax` values obtained from a
non-comparable pair `x,w`.

API note: the conclusion is stated as an inequality between `μmax` on two strict pairs in `ℒ`.
-/
lemma lem2d4₂I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (w : ℒ) (hwI : InIntvl I w)
  (hxw : ¬ x ≤ w)
  (t : ℒ)
  (hxwt : x ⊔ w ≤ t) :
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤
    μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ := by
    have h : ∀ b : ℒ, (h' : x ⊓ w < b ∧ b ≤ x) →
        μ ⟨(x ⊓ w, b), h'.1⟩ ≤ μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ := by
      intro b hb
      have hh : x ⊓ w = b ⊓ w := by
        refine le_antisymm ?_ <| inf_le_inf_right w hb.2
        nth_rw 1 [← inf_idem w, ← inf_assoc]
        exact inf_le_inf_right w <| le_of_lt hb.1
      simp only [hh, ge_iff_le]
      have hbnlew : ¬ b ≤ w := inf_lt_left.mp
        ((congrArg (fun _a ↦ _a < b) (hh.symm)) ▸ hb.1)
      have hfinal : μ ⟨(w, b ⊔ w), right_lt_sup.mpr hbnlew⟩ ≤
        μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt (right_lt_sup.2 hxw)⟩ := by
        apply le_sSup
        use b ⊔ w, ⟨⟨le_sup_right, le_trans (sup_le_sup_right hb.2 w) hxwt⟩,
          (mt right_eq_sup.1) <| inf_lt_left.1 <| hh.symm ▸ hb.1⟩
      apply le_trans (hμcvx.convex b w ⟨le_of_lt (lt_of_le_of_lt (le_inf hxI.1 hwI.1) hb.1),
         le_trans hb.2 hxI.2⟩ hwI hbnlew) hfinal
    apply sSup_le
    rintro b ⟨w_1, ⟨hf₁, hf₂⟩⟩
    rw [hf₂.symm]
    exact h w_1 ⟨lt_of_le_of_ne hf₁.1.1 hf₁.2, hf₁.1.2⟩


/-
Paper Lemma 2.4 (part 3) localized to an interval `I`.

This combines `lem2d4₁` and `lem2d4₂I` to compare `μA` values on two different intervals determined
by the non-comparable pair `x,w`.
-/
lemma lem2d4₃I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (w : ℒ) (hwI : InIntvl I w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) (huxw : u ≤ x ⊓ w) :
  μA μ ⟨(u, x), lt_of_le_of_lt huxw <| inf_lt_left.2 hxw⟩ ≤
    μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩ := by
  apply le_sInf
  rintro imy ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [← hy₂]
  have h₁ : ¬ x ≤ y := by
    by_contra h
    exact lt_irrefl (x ⊔ w) <| lt_of_le_of_lt (sup_le_sup_right h w) <|
      (sup_eq_left.2 hy₁.1.1).symm ▸ lt_of_le_of_ne hy₁.1.2 hy₁.2
  exact le_trans (lem2d4₁ μ x y h₁ u <| le_trans huxw <| inf_le_inf_left x hy₁.1.1)
    <| lem2d4₂I I μ hμcvx x hxI y ⟨le_trans hwI.1 hy₁.1.1, le_trans hy₁.1.2 <| sup_le hxI.2 hwI.2⟩
      h₁ (x ⊔ w) <| sup_le le_sup_left hy₁.1.2


/-
Bundled version of Lemma 2.4 on an interval `I`.

The result returns a triple of inequalities as a nested conjunction, matching the structure used in
the public-facing statement `lemma_2_4` in `Convexity/Results.lean`.
-/
lemma lem2d4I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x) --(hx : I.val.1 ≠ x)
  (w : ℒ) (hwI : InIntvl I w) --(hw : I.val.1 ≠ w)
  (hxw : ¬ x ≤ w)
  (u : ℒ) --(huI : InIntvl I u)
  (t : ℒ) --(htI : InIntvl I t)
  --(hut : u ≤ t)
  (huxw : u ≤ x ⊓ w)
  (hxwt : x ⊔ w ≤ t) :
  μA μ ⟨(u, x), lt_of_le_of_lt huxw <|inf_lt_left.2 hxw⟩ ≤ μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤
    μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ ∧
  μA μ ⟨(u, x), lt_of_le_of_lt huxw <| inf_lt_left.2 hxw⟩ ≤ μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩ :=
  ⟨lem2d4₁ μ x w hxw u huxw,
    ⟨lem2d4₂I I μ hμcvx x hxI w hwI hxw t hxwt, lem2d4₃I I μ hμcvx x hxI w hwI hxw u huxw⟩⟩


/-
Remark 2.5 (part 1), interval-local form: `μmax μ` inherits convexity from `μ`.

This is a key closure property: convexity is preserved by the `μmax` construction.
-/
lemma rmk2d5₁
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  ConvexI I (μmax μ)  :=
  {convex :=fun x y hxI hyI hxy ↦ lem2d4₂I I μ hμcvx x hxI y hyI hxy (x ⊔ y) le_rfl}


/-
Remark 2.5 (part 2): idempotence of `μmax`.

The statement `μmax μ I = μmax (μmax μ) I` says that applying `μmax` twice does not change the
result. Convexity is used to relate the two suprema.
-/
lemma rmk2d5₂
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  μmax μ I = μmax (μmax μ) I := by
  apply eq_of_le_of_ge
  · apply le_sSup
    use I.val.2, ⟨⟨le_of_lt I.prop, le_refl I.val.2⟩, ne_of_lt I.prop⟩
  · apply sSup_le
    simp only [ne_eq, Set.mem_setOf_eq, forall_exists_index]
    intro b v hv res
    rw [← res]
    have h : μmax μ ⟨(v ⊓ I.val.1, v), inf_lt_left.2 (not_le_of_gt (lt_of_le_of_ne hv.1.1 hv.2))⟩ ≤
      μmax μ ⟨(I.val.1, I.val.2),
        lt_of_le_of_lt' ((sup_eq_left.2 hv.1.1).symm ▸ hv.1.2)
          <| right_lt_sup.2 <| not_le_of_gt <| lt_of_le_of_ne hv.1.1 hv.2⟩ :=
      lem2d4₂I I μ hμcvx v hv.1 I.val.1 ⟨le_rfl, le_of_lt I.prop⟩ (not_le_of_gt <|
        lt_of_le_of_ne hv.1.1 hv.2) I.val.2 <| (sup_eq_left.2 hv.1.1).symm ▸ hv.1.2
    simp only [inf_eq_right.2 hv.1.1] at h
    exact h


/-
Remark 2.5 (part 3): invariance of `μA` under replacing `μ` by `μmax μ`.

Together with `rmk2d5₂`, this shows that the outer optimization `μA` is stable under the `μmax`
closure.
-/
lemma rmk2d5₃
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  μA μ I = μA (μmax μ) I := by
  apply eq_of_le_of_ge
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    use a, ha
    apply rmk2d5₂ ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩
    exact Convex_of_Convex_large I
      ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩ ⟨ha.1.1, le_rfl⟩ μ hμcvx
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    use a, ha
    rw [← rmk2d5₂ ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩]
    exact Convex_of_Convex_large I
      ⟨(a, I.val.2), lt_of_le_of_ne ha.1.2 ha.2⟩ ⟨ha.1.1, le_rfl⟩ μ hμcvx


/-
Proposition 2.6 (monotonicity part): `μA (x,z) ≤ μA (y,z)` when `x<y<z`.

This does not use convexity; it is a formal consequence of the definition of `μA` as an infimum.
-/
lemma prop2d6₀
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩  := by
  apply sInf_le_sInf
  simp only [ne_eq, Set.setOf_subset_setOf, forall_exists_index]
  intro u v hv hu
  rw [← hu]
  use v, ⟨⟨le_of_lt <| lt_of_lt_of_le h.1 hv.1.1, hv.1.2⟩, hv.2⟩


/-
Proposition 2.6 (a): a lower bound on `μA (x,z)` by the infimum of the two adjacent `μA` values.

This is the first convexity-dependent inequality in Proposition 2.6.
-/
lemma prop2d6₁I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (z : ℒ) (hzI : InIntvl I z)
  (h : x < y ∧ y < z) :
  (μA μ ⟨(x, y), h.1⟩ ⊓ (μA μ ⟨(y, z), h.2⟩)) ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ := by
  apply le_sInf_iff.2
  rintro d ⟨a, ha, rfl⟩
  by_cases hya : y ≤ a
  · refine le_trans inf_le_right <| sInf_le ?_
    use a, ⟨⟨hya, ha.1.2⟩, ha.2⟩
  · exact le_trans inf_le_left <| le_trans (lem2d4₁ μ y a hya x <| le_inf (le_of_lt h.1) ha.1.1) <|
      lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha.1.1, le_trans ha.1.2 hzI.2⟩ hya z <|
      sup_le (le_of_lt h.2) ha.1.2


/-
Proposition 2.6 (b), case 1: if `μA (x,y) ≥ μA (y,z)` then `μA (y,z) = μA (x,z)`.

This is a clean equality criterion extracted from the general inequality chain.
-/
lemma prop2d6₂I₁
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (z : ℒ) (hzI : InIntvl I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x, y), h.1⟩ ≥ μA μ ⟨(y, z), h.2⟩) :
  μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
  := le_antisymm ((inf_eq_right.2 h').symm ▸
    prop2d6₁I I μ hμcvx x hxI y hyI z hzI h) <| prop2d6₀ μ x y z h


/-
Proposition 2.6 (b), case 2: if `μA (x,y) < μA (y,z)` then `μA (x,y) ≤ μA (x,z) ≤ μA (y,z)`.

This provides the comparison bounds needed for the strict-inequality branch.
-/
lemma prop2d6₂I₂
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (z : ℒ) (hzI : InIntvl I z)
  (h : x < y ∧ y < z)
  (h' : μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩) :
  μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩
  := ⟨(inf_eq_left.2 <| le_of_lt h').symm ▸
    prop2d6₁I I μ hμcvx x hxI y hyI z hzI h, prop2d6₀ μ x y z h⟩


/-
Helper lemma: unpack `IsComparable x y` into a useful disjunction for strict/weak comparisons.

This is a small propositional normalization used in the proof of `prop2d6₃I`.
-/
lemma comparable_iff {L : Type*} [PartialOrder L]
(x : L) (y : L)
(h : IsComparable x y) :
x < y ∨ y ≤ x := by
  simp only [IsComparable] at h
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt] at h
  nth_rw 2 [or_comm] at h
  rw [or_assoc] at h
  nth_rw 2 [←or_assoc, eq_comm] at h
  rwa [or_self, eq_comm, ← le_iff_eq_or_lt] at h


/-
Proposition 2.6 (c): a case split yielding either equality or a strict inequality chain.

The hypothesis allows either comparability of the two adjacent `μA` values, or attainment of the
infimum defining `μA (x,z)`. The conclusion then provides a dichotomy between equality and a strict
improvement.
-/
lemma prop2d6₃I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (z : ℒ) (hzI : InIntvl I z)
  (h : x < y ∧ y < z)
  (h' : (IsComparable (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩)) ∨
        (IsAttained μ ⟨(x, z), lt_trans h.1 h.2⟩)) :
  μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨
  (μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
   μA μ ⟨(x, z), lt_trans h.1 h.2⟩ < μA μ ⟨(y, z), h.2⟩) := by
  rcases h' with h₁ | h₂
  · apply comparable_iff (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩) at h₁
    by_cases h₂ : μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
    · exact Or.inl h₂
    · have h₃ : μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩ := Or.resolve_right h₁ (fun hcontra ↦
      h₂ (prop2d6₂I₁ I μ hμcvx x hxI y hyI z hzI h hcontra))
      have h₄ : μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
        μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩ :=
          prop2d6₂I₂ I μ hμcvx x hxI y hyI z hzI h h₃
      exact Or.inr ⟨h₄.1, lt_of_le_of_ne h₄.2 (Ne.symm h₂)⟩
  · rcases h₂ with ⟨a, ⟨ha₁, ⟨ha₂, hres⟩⟩⟩
    apply or_iff_not_imp_left.2
    intro hnot
    have h' : ¬ y ≤ a := by
      by_contra hcontra
      have h''' : μA μ ⟨(y, z), h.2⟩ ≤ μmax μ ⟨(a, z), lt_of_le_of_ne ha₁.2 ha₂⟩ := by
          apply sInf_le
          use a , ⟨⟨hcontra, ha₁.2⟩, ha₂⟩
      exact hnot <| eq_of_le_of_ge (hres ▸ h''') <| prop2d6₀ μ x y z h
    exact ⟨hres ▸ (le_trans (lem2d4₁ μ y a h' x (le_inf (le_of_lt h.1) ha₁.1)) <|
      lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha₁.1, le_trans ha₁.2 hzI.2⟩ h' z <|
      sup_le (le_of_lt h.2) ha₁.2),lt_of_le_of_ne (prop2d6₀ μ x y z h) <| Ne.symm hnot⟩


/-
Remark 2.7: in a complete linear order, a strict improvement on the left forces equality on the
right.

This is a specialization of `prop2d6₃I` to the total interval and uses totality of `≤` on `S`.
-/
lemma rmk2d7
  {S : Type*} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI ⟨(⊥, ⊤), bot_lt_top⟩ μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥, x), h.1⟩ > μA μ ⟨(⊥, ⊤), bot_lt_top⟩) :
  μA μ ⟨(x, ⊤), h.2⟩ = μA μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    have h₁ : μA μ ⟨(x, ⊤), h.2⟩ = μA μ ⟨(⊥, ⊤), bot_lt_top⟩ ∨
      (μA μ ⟨(⊥, x), h.1⟩ ≤ μA μ ⟨(⊥, ⊤), bot_lt_top⟩ ∧
      μA μ ⟨(⊥, ⊤), bot_lt_top⟩ < μA μ ⟨(x, ⊤), h.2⟩) := by
      apply prop2d6₃I ⟨(⊥, ⊤), bot_lt_top⟩ μ hμcvx ⊥ ⟨le_rfl, le_of_lt bot_lt_top⟩
        x ⟨le_of_lt h.1, le_top⟩ ⊤ ⟨le_of_lt bot_lt_top, le_rfl⟩ h
      exact Or.inl <| le_total (μA μ ⟨(⊥, x), h.1⟩) (μA μ ⟨(x, ⊤), h.2⟩)
    rcases h₁ with h₂ | h₃
    · exact h₂
    · exact Classical.byContradiction fun x_1 ↦ not_le_of_gt h' h₃.left


/-
Proposition 2.8 (auxiliary step): a disjunction bounding one of two `μA` values by a `μmax` value.

This is an interval-local statement used to derive the “meet” inequality in Proposition 2.8.
-/
lemma prop2d8₀I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (u : ℒ) (h : u < x ∧ u < y)
  (w : ℒ) (hwI : InIntvl I w)
  (hw : u ≤ w ∧ w < x ⊔ y) :
  μA μ ⟨(u, x), h.1⟩ ≤ μmax μ ⟨(w, x ⊔ y), hw.2⟩ ∨
  μA μ ⟨(u, y), h.2⟩ ≤ μmax μ ⟨(w, x ⊔ y), hw.2⟩ := by
  have h' : ¬ x ≤ w ∨ ¬ y ≤ w := by
    apply not_and_or.1
    rw [← sup_le_iff]
    apply not_le_of_gt hw.2
  rcases h' with h₁ | h₂
  · exact Or.inl <| le_trans (lem2d4₁ μ x w h₁ u <| le_inf (le_of_lt h.1) hw.1) <|
      lem2d4₂I I μ hμcvx x hxI w hwI h₁ (x ⊔ y) <| sup_le le_sup_left <| le_of_lt hw.2
  · exact Or.inr <| le_trans (lem2d4₁ μ y w h₂ u <| le_inf (le_of_lt h.2) hw.1) <|
      lem2d4₂I I μ hμcvx y hyI w hwI h₂ (x ⊔ y) <| sup_le le_sup_right <| le_of_lt hw.2


/-
Proposition 2.8 (a): `μA (u, x ⊔ y)` dominates the meet `μA (u,x) ⊓ μA (u,y)`.

This is obtained by taking an infimum and using `prop2d8₀I` to select the relevant branch.
-/
lemma prop2d8₁I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (u : ℒ) (huI : InIntvl I u)
  (h : u < x ∧ u < y) :
  μA μ ⟨(u, x), h.1⟩ ⊓ μA μ ⟨(u, y), h.2⟩ ≤ μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ := by
  apply le_sInf_iff.2
  rintro d ⟨w, hw, rfl⟩
  have h' : μA μ ⟨(u, x), h.1⟩ ≤ μmax μ ⟨(w, x ⊔ y), lt_of_le_of_ne hw.1.2 hw.2⟩ ∨
  μA μ ⟨(u, y), h.2⟩ ≤ μmax μ ⟨(w, x ⊔ y), lt_of_le_of_ne hw.1.2 hw.2⟩ :=
    prop2d8₀I I μ hμcvx x hxI y hyI u h w ⟨le_trans huI.1 hw.1.1, le_trans hw.1.2 <|
      sup_le hxI.2 hyI.2⟩ ⟨hw.1.1,lt_of_le_of_ne hw.1.2 hw.2⟩
  rcases h' with h₁ | h₂
  · exact le_trans inf_le_left h₁
  · exact le_trans inf_le_right h₂


/-
Proposition 2.8 (b): under comparability or attainment, one of the two `μA` values is dominated by
`μA (u, x ⊔ y)`.

This is a “one-sided dominance” conclusion that matches the alternative in the paper statement.
-/
lemma prop2d8₂I
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
  (x : ℒ) (hxI : InIntvl I x)
  (y : ℒ) (hyI : InIntvl I y)
  (u : ℒ) (huI : InIntvl I u)
  (h : u < x ∧ u < y)
  (hcpb : IsComparable (μA μ ⟨(u, x), h.1⟩)
  (μA μ ⟨(u, y), h.2⟩) ∨ IsAttained μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩) :
  μA μ ⟨(u, x), h.1⟩ ≤ μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ∨
  μA μ ⟨(u, y), h.2⟩ ≤ μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ := by
  rcases hcpb with h₁ | h₂
  · rcases h₁ with h₃ | h₄
    · exact Or.inl <| (inf_eq_left.2 h₃).symm ▸ (prop2d8₁I I μ hμcvx x hxI y hyI u huI h)
    · have h' : μA μ ⟨(u, x), h.1⟩ ⊓ μA μ ⟨(u, y), h.2⟩ ≤ μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩
        := prop2d8₁I I μ hμcvx x hxI y hyI u huI h
      rw [inf_comm] at h'
      exact Or.inr <| (inf_eq_left.2 h₄).symm ▸ h'
  · rcases h₂ with ⟨a, ha, ⟨ha',ha''⟩⟩
    exact ha'' ▸ (prop2d8₀I I μ hμcvx x hxI y hyI u h a ⟨le_trans huI.1 ha.1, le_trans ha.2 <|
      sup_le hxI.2 hyI.2⟩ ⟨ha.1,lt_of_le_of_ne ha.2 ha'⟩)

end

end impl

end HarderNarasimhan
