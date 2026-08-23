/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Defs
import Mathlib.Tactic.Common

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

/--
Convexity on the total interval is equivalent to global convexity.

This lemma bridges the localized class `ConvexI TotIntvl μ` and the global class `Convex μ`.
It is marked `[simp]` so that typeclass conversions can be reduced automatically.
-/
@[simp]
lemma ConvexI_TotIntvl_iff_Convex {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : ConvexI TotIntvl μ ↔
Convex μ :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.convex x y (in_TotIntvl _) (in_TotIntvl _) hxy⟩,
    fun h ↦ ⟨fun x y _ _ hxy ↦ h.convex x y hxy⟩⟩

/--
Typeclass instance: a globally convex `μ` induces interval-local convexity on the total interval.

This is a convenience instance so that `Convex μ` can be used wherever `ConvexI TotIntvl μ` is
expected.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} [Convex μ] :
ConvexI TotIntvl μ :=
  (ConvexI_TotIntvl_iff_Convex μ).mpr inferInstance

/--
Typeclass instance: interval-local convexity on the total interval implies global convexity.

This is the reverse direction of the previous instance.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} [ConvexI TotIntvl μ] :
Convex μ :=
  (ConvexI_TotIntvl_iff_Convex μ).mp inferInstance


section

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
variable {S : Type*} [CompleteLattice S]

/--
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
    apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    exact ⟨a, ⟨⟨le_trans huxw ha.1.1, ha.1.2⟩, ha.2⟩, rfl⟩
  exact le_trans h1 <| sInf_le ⟨x ⊓ w, ⟨⟨le_rfl, (inf_lt_left.2 hxw).le⟩,
    (inf_lt_left.2 hxw).ne⟩, rfl⟩


/--
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
    let target := μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩
    have h : ∀ b : ℒ, (h' : x ⊓ w < b ∧ b ≤ x) → μ ⟨(x ⊓ w, b), h'.1⟩ ≤ target := by
      intro b hb
      have hh : x ⊓ w = b ⊓ w :=
        le_antisymm (le_inf hb.1.le inf_le_right) (inf_le_inf_right w hb.2)
      have hbnlew : ¬ b ≤ w := inf_lt_left.mp (hh ▸ hb.1)
      simp only [hh]
      exact le_trans (hμcvx.convex b w ⟨le_of_lt (lt_of_le_of_lt (le_inf hxI.1 hwI.1) hb.1),
        le_trans hb.2 hxI.2⟩ hwI hbnlew) <| le_sSup ⟨b ⊔ w, ⟨⟨le_sup_right,
        le_trans (sup_le_sup_right hb.2 w) hxwt⟩, mt right_eq_sup.1 hbnlew⟩, rfl⟩
    apply sSup_le
    rintro b ⟨w_1, hf₁, rfl⟩
    exact h w_1 ⟨lt_of_le_of_ne hf₁.1.1 hf₁.2, hf₁.1.2⟩


/--
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
  rintro imy ⟨y, hy₁, rfl⟩
  have h₁ : ¬ x ≤ y := fun h ↦ lt_irrefl (x ⊔ w) <| lt_of_le_of_lt (sup_le_sup_right h w) <|
    (sup_eq_left.2 hy₁.1.1).symm ▸ lt_of_le_of_ne hy₁.1.2 hy₁.2
  exact le_trans (lem2d4₁ μ x y h₁ u <| le_trans huxw <| inf_le_inf_left x hy₁.1.1)
    <| lem2d4₂I I μ hμcvx x hxI y ⟨le_trans hwI.1 hy₁.1.1, le_trans hy₁.1.2 <| sup_le hxI.2 hwI.2⟩
      h₁ (x ⊔ w) <| sup_le le_sup_left hy₁.1.2


/--
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
  ⟨lem2d4₁ μ x w hxw u huxw, lem2d4₂I I μ hμcvx x hxI w hwI hxw t hxwt,
    lem2d4₃I I μ hμcvx x hxI w hwI hxw u huxw⟩


/--
Remark 2.5 (part 1), interval-local form: `μmax μ` inherits convexity from `μ`.

This is a key closure property: convexity is preserved by the `μmax` construction.
-/
lemma rmk2d5₁
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  ConvexI I (μmax μ)  :=
  ⟨fun x y hxI hyI hxy ↦ lem2d4₂I I μ hμcvx x hxI y hyI hxy (x ⊔ y) le_rfl⟩


/--
Remark 2.5 (part 2): idempotence of `μmax`.

The statement `μmax μ I = μmax (μmax μ) I` says that applying `μmax` twice does not change the
result. Convexity is used to relate the two suprema.
-/
lemma rmk2d5₂
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  μmax μ I = μmax (μmax μ) I := by
  apply eq_of_le_of_ge
  · exact le_sSup ⟨I.val.2, ⟨⟨le_of_lt I.prop, le_rfl⟩, ne_of_lt I.prop⟩, rfl⟩
  · apply sSup_le
    rintro b ⟨v, hv, rfl⟩
    simpa only [inf_eq_right.2 hv.1.1] using
      lem2d4₂I I μ hμcvx v hv.1 I.val.1 ⟨le_rfl, le_of_lt I.prop⟩ (not_le_of_gt <|
        lt_of_le_of_ne hv.1.1 hv.2) I.val.2 <| (sup_eq_left.2 hv.1.1).symm ▸ hv.1.2


/--
Remark 2.5 (part 3): invariance of `μA` under replacing `μ` by `μmax μ`.

Together with `rmk2d5₂`, this shows that the outer optimization `μA` is stable under the `μmax`
closure.
-/
lemma rmk2d5₃
  (I : {p : ℒ × ℒ // p.1 < p.2})
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ) :
  μA μ I = μA (μmax μ) I := by
  have key : ∀ a, I.val.1 ≤ a → ∀ h : a < I.val.2,
      μmax μ ⟨(a, I.val.2), h⟩ = μmax (μmax μ) ⟨(a, I.val.2), h⟩ :=
    fun a ha h ↦ rmk2d5₂ ⟨(a, I.val.2), h⟩ μ <|
      Convex_of_Convex_large I ⟨(a, I.val.2), h⟩ ⟨ha, le_rfl⟩ μ hμcvx
  apply eq_of_le_of_ge
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    exact ⟨a, ha, key a ha.1.1 _⟩
  · apply sInf_le_sInf
    rintro t ⟨a, ha, rfl⟩
    exact ⟨a, ha, (key a ha.1.1 _).symm⟩


/--
Proposition 2.6 (monotonicity part): `μA (x,z) ≤ μA (y,z)` when `x<y<z`.

This does not use convexity; it is a formal consequence of the definition of `μA` as an infimum.
-/
lemma prop2d6₀
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩  := by
  apply sInf_le_sInf
  rintro u ⟨v, hv, rfl⟩
  exact ⟨v, ⟨⟨le_of_lt <| lt_of_lt_of_le h.1 hv.1.1, hv.1.2⟩, hv.2⟩, rfl⟩


/--
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
  apply le_sInf
  rintro d ⟨a, ha, rfl⟩
  by_cases hya : y ≤ a
  · exact le_trans inf_le_right <| sInf_le ⟨a, ⟨⟨hya, ha.1.2⟩, ha.2⟩, rfl⟩
  · exact le_trans inf_le_left <| le_trans (lem2d4₁ μ y a hya x <| le_inf (le_of_lt h.1) ha.1.1) <|
      lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha.1.1, le_trans ha.1.2 hzI.2⟩ hya z <|
      sup_le (le_of_lt h.2) ha.1.2


/--
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
  := le_antisymm (le_trans (le_inf h' le_rfl) <|
    prop2d6₁I I μ hμcvx x hxI y hyI z hzI h) <| prop2d6₀ μ x y z h


/--
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
  := ⟨le_trans (le_inf le_rfl h'.le) <|
    prop2d6₁I I μ hμcvx x hxI y hyI z hzI h, prop2d6₀ μ x y z h⟩


/--
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
  · by_cases h₂ : μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
    · exact Or.inl h₂
    · have hne : ¬ μA μ ⟨(y, z), h.2⟩ ≤ μA μ ⟨(x, y), h.1⟩ :=
        fun hc ↦ h₂ (prop2d6₂I₁ I μ hμcvx x hxI y hyI z hzI h hc)
      obtain ⟨h₃, h₄⟩ := prop2d6₂I₂ I μ hμcvx x hxI y hyI z hzI h <|
        lt_of_le_not_ge (h₁.resolve_right hne) hne
      exact Or.inr ⟨h₃, lt_of_le_of_ne h₄ (Ne.symm h₂)⟩
  · rcases h₂ with ⟨a, ha₁, ha₂, hres⟩
    refine or_iff_not_imp_left.2 fun hnot ↦ ?_
    have h' : ¬ y ≤ a := fun hcontra ↦ hnot <| eq_of_le_of_ge
      (hres ▸ sInf_le ⟨a, ⟨⟨hcontra, ha₁.2⟩, ha₂⟩, rfl⟩) (prop2d6₀ μ x y z h)
    exact ⟨hres ▸ (le_trans (lem2d4₁ μ y a h' x (le_inf (le_of_lt h.1) ha₁.1)) <|
      lem2d4₂I I μ hμcvx y hyI a ⟨le_trans hxI.1 ha₁.1, le_trans ha₁.2 hzI.2⟩ h' z <|
      sup_le (le_of_lt h.2) ha₁.2), lt_of_le_of_ne (prop2d6₀ μ x y z h) <| Ne.symm hnot⟩


/--
Remark 2.7: in a complete linear order, a strict improvement on the left forces equality on the
right.

This is a specialization of `prop2d6₃I` to the total interval and uses totality of `≤` on `S`.
-/
lemma rmk2d7
  {S : Type*} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI ⟨(⊥, ⊤), bot_lt_top⟩ μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥, x), h.1⟩ > μA μ ⟨(⊥, ⊤), bot_lt_top⟩) :
  μA μ ⟨(x, ⊤), h.2⟩ = μA μ ⟨(⊥, ⊤), bot_lt_top⟩ :=
  (prop2d6₃I ⟨(⊥, ⊤), bot_lt_top⟩ μ hμcvx ⊥ ⟨le_rfl, le_top⟩
      x ⟨bot_le, le_top⟩ ⊤ ⟨bot_le, le_rfl⟩ h
      (Or.inl <| le_total _ _)).resolve_right
    fun h₃ ↦ not_le_of_gt h' h₃.1


/--
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
  rcases not_and_or.1 (fun hc ↦ not_le_of_gt hw.2 (sup_le hc.1 hc.2)) with h₁ | h₂
  · exact Or.inl <| le_trans (lem2d4₁ μ x w h₁ u <| le_inf (le_of_lt h.1) hw.1) <|
      lem2d4₂I I μ hμcvx x hxI w hwI h₁ (x ⊔ y) <| sup_le le_sup_left <| le_of_lt hw.2
  · exact Or.inr <| le_trans (lem2d4₁ μ y w h₂ u <| le_inf (le_of_lt h.2) hw.1) <|
      lem2d4₂I I μ hμcvx y hyI w hwI h₂ (x ⊔ y) <| sup_le le_sup_right <| le_of_lt hw.2


/--
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
  apply le_sInf
  rintro d ⟨w, hw, rfl⟩
  exact (prop2d8₀I I μ hμcvx x hxI y hyI u h w ⟨le_trans huI.1 hw.1.1, le_trans hw.1.2 <|
      sup_le hxI.2 hyI.2⟩ ⟨hw.1.1, lt_of_le_of_ne hw.1.2 hw.2⟩).elim
    (le_trans inf_le_left) (le_trans inf_le_right)


/--
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
    · exact Or.inl <| le_trans (le_inf le_rfl h₃) <| prop2d8₁I I μ hμcvx x hxI y hyI u huI h
    · exact Or.inr <| le_trans (le_inf h₄ le_rfl) <| prop2d8₁I I μ hμcvx x hxI y hyI u huI h
  · rcases h₂ with ⟨a, ha, ha', ha''⟩
    exact ha'' ▸ (prop2d8₀I I μ hμcvx x hxI y hyI u h a ⟨le_trans huI.1 ha.1, le_trans ha.2 <|
      sup_le hxI.2 hyI.2⟩ ⟨ha.1, lt_of_le_of_ne ha.2 ha'⟩)

end

end impl

end HarderNarasimhan
