/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Basic
import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl

/-!
This file contains the public-facing results of the convexity module.

Compared to `HarderNarasimhan.Convexity.Impl`, the statements here are intended as stable API:
they package the implementation lemmas into clean theorems that closely match the numbering and
structure in the accompanying paper.

Main results:
- `lemma_2_4`: the fundamental inequality chain derived from convexity.
- `remark_2_5`: closure and idempotence properties of `μmax`, and invariance of `μA`.
- `proposition_2_6` and `proposition_2_8`: structural consequences of convexity for `μA`.
- `remark_2_7`: a linear-order specialization.
- `ConvexI_iff_Convex_res`: equivalence between interval-local convexity and global convexity of
  `Resμ`.
-/

namespace HarderNarasimhan

/-
Lemma 2.4 (paper-facing form).

Assuming global convexity of `μ`, this provides the two inequalities labelled (2.2) and (2.3) in the
file, packaged as a conjunction.

API note: the proof reduces to the interval-local lemmas in `HarderNarasimhan.Convexity.Impl` by
using the equivalence `ConvexI TotIntvl μ ↔ Convex μ`.
-/
lemma lemma_2_4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (x : ℒ) (w : ℒ) (hxw : ¬ x ≤ w)
  (u : ℒ) (t : ℒ)
  (huxw : u ≤ x ⊓ w) (hxwt : x ⊔ w ≤ t) :
------------
  (
  --`(2.2)`
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤
    μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ∧
  μmax μ ⟨(x ⊓ w, x), inf_lt_left.2 hxw⟩ ≤
    μmax μ ⟨(w, t), lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩
  ) ∧
  --`(2.3)`
  μA μ ⟨(u, x), lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤ μA μ ⟨(w, x ⊔ w), right_lt_sup.2 hxw⟩
------------
  := by
    apply (impl.ConvexI_TotIntvl_iff_Convex _).2 at hμcvx
    exact ⟨⟨impl.lem2d4₁ μ x w hxw u huxw,impl.lem2d4₂I TotIntvl μ hμcvx x (in_TotIntvl x) w
      (in_TotIntvl w) hxw t hxwt⟩,impl.lem2d4₃I TotIntvl μ hμcvx x
      (in_TotIntvl x) w (in_TotIntvl w) hxw u huxw⟩


/-
Remark 2.5 (paper-facing form).

Under convexity, this states:
- `μmax μ` is convex, and
- `μmax` is idempotent and leaves `μA` unchanged on every interval.

API note: the second component is universally quantified over intervals to facilitate rewriting in
later files.
-/
lemma remark_2_5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ) :
------------
  Convex (μmax μ) ∧
  ∀  I : {p : ℒ × ℒ // p.1 < p.2},
    μmax μ I = μmax (μmax μ) I ∧ μA μ I = μA (μmax μ) I
------------
  := by
    apply (impl.ConvexI_TotIntvl_iff_Convex _).2 at hμcvx
    rw [← impl.ConvexI_TotIntvl_iff_Convex]
    exact ⟨impl.rmk2d5₁ TotIntvl μ hμcvx,fun I ↦ ⟨impl.rmk2d5₂ I μ
      (Convex_of_Convex_large TotIntvl I ⟨bot_le,le_top⟩ μ hμcvx),
      impl.rmk2d5₃ I μ (Convex_of_Convex_large TotIntvl I ⟨bot_le,le_top⟩ μ hμcvx)⟩⟩


/-
Proposition 2.6 (paper-facing form).

For `x<y<z`, the statement consists of:
- the unconditional monotonicity `μA (x,z) ≤ μA (y,z)`, and
- under convexity, parts (a), (b), (c) giving refined comparisons/equalities involving `μA`.

API note: the proposition is packaged as a nested conjunction/implication structure mirroring the
paper.
-/
lemma proposition_2_6 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S)
  (x : ℒ) (y : ℒ) (z : ℒ)
  (h : x < y ∧ y < z) :
------------
  --`(2.4)`
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩ ∧
  (
  Convex μ →
  --`(a)`
  μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≥ (μA μ ⟨(x, y), h.1⟩ ⊓ (μA μ ⟨(y, z), h.2⟩))
  ∧ (
  --`(b)`
  (
  μA μ ⟨(x, y), h.1⟩ ≥ μA μ ⟨(y, z), h.2⟩ →
    μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩
  ) ∧ (
  μA μ ⟨(x, y), h.1⟩ < μA μ ⟨(y, z), h.2⟩ →
    μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
    μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ≤ μA μ ⟨(y, z), h.2⟩
  )
  ) ∧ (
  --`(c)`
  IsComparable (μA μ ⟨(x, y), h.1⟩) (μA μ ⟨(y, z), h.2⟩) ∨
  IsAttained μ ⟨(x, z), lt_trans h.1 h.2⟩ →
    μA μ ⟨(y, z), h.2⟩ = μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∨
    (μA μ ⟨(x, y), h.1⟩ ≤ μA μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧
     μA μ ⟨(x, z), lt_trans h.1 h.2⟩ < μA μ ⟨(y, z), h.2⟩)
    )
  )
------------
:= by
  rw [← impl.ConvexI_TotIntvl_iff_Convex]
  exact ⟨impl.prop2d6₀ μ x y z h, fun hμcvx ↦ ⟨impl.prop2d6₁I TotIntvl μ hμcvx x (in_TotIntvl x)
    y (in_TotIntvl y) z (in_TotIntvl z) h,⟨⟨impl.prop2d6₂I₁ TotIntvl μ hμcvx x (in_TotIntvl x) y
    (in_TotIntvl y) z (in_TotIntvl z) h,impl.prop2d6₂I₂ TotIntvl μ hμcvx x (in_TotIntvl x) y
    (in_TotIntvl y) z (in_TotIntvl z) h⟩,impl.prop2d6₃I TotIntvl μ hμcvx x (in_TotIntvl x) y
    (in_TotIntvl y) z (in_TotIntvl z) h⟩⟩⟩


/-
Remark 2.7 (paper-facing form).

In a complete linear order, if the left subinterval gives a strictly larger `μA` value than the
total interval, then the right subinterval must have `μA` equal to the total interval value.

API note: this is stated with `μA μ TotIntvl` to use the abbreviation for the total interval.
-/
lemma remark_2_7 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLinearOrder S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (x : ℒ) (h : ⊥ < x ∧ x < ⊤)
  (h' : μA μ ⟨(⊥, x), h.1⟩ > μA μ TotIntvl) :
------------
  μA μ ⟨(x, ⊤), h.2⟩ = μA μ TotIntvl
------------
:= by
  rw [← impl.ConvexI_TotIntvl_iff_Convex] at hμcvx
  exact impl.rmk2d7 μ hμcvx x h h'


/-
Proposition 2.8 (paper-facing form).

Under convexity, `μA (u, x ⊔ y)` dominates the meet of the two values `μA (u,x)` and `μA (u,y)`.
Moreover, under an additional hypothesis (comparability or attainment), one of these two values is
itself dominated by `μA (u, x ⊔ y)`.
-/
lemma proposition_2_8 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S]
  (μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : Convex μ)
  (x : ℒ) (y : ℒ) (u : ℒ)
  (h : u < x ∧ u < y) :
------------
  --`(a)`
  μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ⊓ μA μ ⟨(u, y), h.2⟩
  ∧ (
  --`(b)`
  IsComparable (μA μ ⟨(u, x), h.1⟩) (μA μ ⟨(u, y), h.2⟩) ∨
  IsAttained μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ →
    μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, x), h.1⟩ ∨
    μA μ ⟨(u, x ⊔ y), lt_sup_of_lt_left h.1⟩ ≥ μA μ ⟨(u, y), h.2⟩
  )
------------
:= by
  apply (impl.ConvexI_TotIntvl_iff_Convex _).2 at hμcvx
  exact ⟨impl.prop2d8₁I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) u (in_TotIntvl u) h,
  impl.prop2d8₂I TotIntvl μ hμcvx x (in_TotIntvl x) y (in_TotIntvl y) u (in_TotIntvl u) h⟩

/-
User-facing equivalence between localized convexity and convexity of the restricted measure.

This is essentially `impl.ConvexI_iff_Convex_Res`, but presented as a theorem in the public
namespace. It enables rewriting convexity hypotheses when switching between an interval `I` in `ℒ`
and the subtype `Interval I` equipped with the restricted function `Resμ I μ`.
-/
theorem ConvexI_iff_Convex_res {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2}) (μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
ConvexI I μ ↔ Convex (Resμ I μ) := by
  rw [← impl.ConvexI_TotIntvl_iff_Convex]
  constructor
  · exact fun h ↦ { convex := fun x y hx hy hxy ↦ h.convex x y x.prop y.prop hxy }
  · exact fun h ↦
      { convex := fun x y hx hy hxy ↦ h.convex ⟨x,hx⟩ ⟨y,hy⟩ (in_TotIntvl _) (in_TotIntvl _) hxy }

end HarderNarasimhan
