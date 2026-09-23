/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict
public import Mathlib.Tactic.Common

/-!
# Convex payoff functions

A payoff function on a lattice is convex if `μ (x ⊓ y, x) ≤ μ (y, x ⊔ y)` whenever
`¬ x ≤ y`. Thus convexity compares intervals with endpoints related by meet and join.
An affine payoff function satisfies equality in this comparison.

Convexity is also defined on an interval. It passes to subintervals and is equivalent to
convexity of the restricted payoff function.

## Main definitions

* `HarderNarasimhan.PayoffFunction.IsConvex`: convexity of a payoff function.
* `HarderNarasimhan.PayoffFunction.IsConvexOn`: convexity on an interval.
* `HarderNarasimhan.PayoffFunction.IsAffine`: equality in the convexity condition.

## Main results

* `HarderNarasimhan.PayoffFunction.IsConvexOn.A_le_A_sup`: comparison of game values on
  intervals related by meet and join.
* `HarderNarasimhan.PayoffFunction.IsConvexOn.max`: convexity is preserved by `max`.
* `HarderNarasimhan.PayoffFunction.IsConvexOn.A_eq_or_lt`: comparison of game values when an
  interval is split at an intermediate point.
* `HarderNarasimhan.PayoffFunction.IsConvexOn.A_le_A_sup_or`: comparison of game values on
  two intervals with the same left endpoint and on their join.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [CompleteLattice S]

/-! ### The convexity typeclasses -/

/-- A payoff function is convex if `μ (x ⊓ y, x) ≤ μ (y, x ⊔ y)` whenever `¬ x ≤ y`.
The latter condition ensures that both intervals are strict. -/
class IsConvex (μ : PayoffFunction ℒ S) : Prop where
  /-- The convexity inequality. -/
  le : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/-- A payoff function is convex on `I` if the convexity inequality holds for every
`x, y ∈ I` with `¬ x ≤ y`. -/
class IsConvexOn (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop where
  /-- The convexity inequality, for pairs in `I`. -/
  le : ∀ x y : ℒ, x ∈ I → y ∈ I → (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Convexity on an interval implies convexity on each subinterval. -/
lemma IsConvexOn.mono {I₁ I₂ : StrictIntvl ℒ} (h : μ.IsConvexOn I₁) (hI : I₂ ≤ I₁) :
    μ.IsConvexOn I₂ :=
  ⟨fun x y hx hy hxy ↦ h.le x y ⟨le_trans hI.1 hx.1, le_trans hx.2 hI.2⟩
    ⟨le_trans hI.1 hy.1, le_trans hy.2 hI.2⟩ hxy⟩

section Top

variable [Nontrivial ℒ] [BoundedOrder ℒ]

/-- Convexity on the total interval `⊤` is the same as global convexity. -/
@[simp] lemma isConvexOn_top_iff : μ.IsConvexOn ⊤ ↔ μ.IsConvex :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.le x y (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxy⟩,
    fun h ↦ ⟨fun x y _ _ hxy ↦ h.le x y hxy⟩⟩

instance [μ.IsConvex] : μ.IsConvexOn ⊤ := isConvexOn_top_iff.mpr inferInstance

instance [μ.IsConvexOn ⊤] : μ.IsConvex := isConvexOn_top_iff.mp inferInstance

end Top

/-- Convexity on `I` is equivalent to convexity of the restriction to the points of `I`. -/
theorem isConvexOn_iff_isConvex_restrict : μ.IsConvexOn I ↔ (μ.restrict I).IsConvex :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.le x y x.prop y.prop hxy⟩,
    fun h ↦ ⟨fun x y hx hy hxy ↦ h.le ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩⟩

/-- A payoff function is affine if `μ (x ⊓ y, x) = μ (y, x ⊔ y)` whenever `¬ x ≤ y`. -/
class IsAffine (μ : PayoffFunction ℒ S) : Prop where
  /-- The affine equality. -/
  eq : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ = μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/-- An affine payoff function is convex. -/
instance IsAffine.toIsConvex [haff : μ.IsAffine] : μ.IsConvex :=
  ⟨fun x y hxy ↦ (haff.eq x y hxy).le⟩

/-- Restriction preserves the affine property. -/
instance [haff : μ.IsAffine] : (μ.restrict I).IsAffine :=
  ⟨fun x y h ↦ haff.eq x y h⟩

/-! ### Comparisons across meets and joins -/

/-- If `u ≤ x ⊓ w` and `¬ x ≤ w`, then `μ.A (u, x) ≤ μ.max (x ⊓ w, x)`. -/
lemma A_le_max_inf (μ : PayoffFunction ℒ S) {x w u : ℒ} (hxw : ¬ x ≤ w) (huxw : u ≤ x ⊓ w) :
    μ.A ⟨u, x, lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤
      μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ :=
  A_le ⟨huxw, inf_lt_left.2 hxw⟩

/-- For a payoff function convex on `I`, `μ.max (x ⊓ w, x) ≤ μ.max (w, t)` whenever
`x, w ∈ I`, `¬ x ≤ w` and `x ⊔ w ≤ t`. -/
lemma IsConvexOn.max_inf_le_max (hμcvx : μ.IsConvexOn I) {x w t : ℒ}
    (hxI : x ∈ I) (hwI : w ∈ I) (hxw : ¬ x ≤ w) (hxwt : x ⊔ w ≤ t) :
    μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ ≤
      μ.max ⟨w, t, lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ := by
  refine max_le fun b hb ↦ ?_
  have hinf : x ⊓ w = b ⊓ w :=
    le_antisymm (le_inf hb.1.le inf_le_right) (inf_le_inf_right w hb.2)
  have hbw : ¬ b ≤ w := inf_lt_left.mp (hinf ▸ hb.1)
  have hbI : b ∈ I := ⟨(le_inf hxI.1 hwI.1).trans hb.1.le, hb.2.trans hxI.2⟩
  calc
    μ ⟨x ⊓ w, b, hb.1⟩ = μ ⟨b ⊓ w, b, inf_lt_left.2 hbw⟩ :=
      congrArg μ (StrictIntvl.ext hinf rfl)
    _ ≤ μ ⟨w, b ⊔ w, right_lt_sup.2 hbw⟩ := hμcvx.le b w hbI hwI hbw
    _ ≤ μ.max ⟨w, t, lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ :=
      le_max (I := ⟨w, t, lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩)
        ⟨right_lt_sup.2 hbw, (sup_le_sup_right hb.2 w).trans hxwt⟩

/-- For a payoff function convex on `I`, `μ.A (u, x) ≤ μ.A (w, x ⊔ w)` whenever
`x, w ∈ I`, `¬ x ≤ w` and `u ≤ x ⊓ w`. -/
lemma IsConvexOn.A_le_A_sup (hμcvx : μ.IsConvexOn I) {x w u : ℒ}
    (hxI : x ∈ I) (hwI : w ∈ I) (hxw : ¬ x ≤ w) (huxw : u ≤ x ⊓ w) :
    μ.A ⟨u, x, lt_of_le_of_lt huxw <| inf_lt_left.2 hxw⟩ ≤
      μ.A ⟨w, x ⊔ w, right_lt_sup.2 hxw⟩ := by
  refine le_A fun y hy ↦ ?_
  have hxy : ¬ x ≤ y := fun hxy ↦ hy.2.not_ge (sup_le hxy hy.1)
  have hyI : y ∈ I := ⟨hwI.1.trans hy.1, hy.2.le.trans (sup_le hxI.2 hwI.2)⟩
  calc
    μ.A ⟨u, x, lt_of_le_of_lt huxw <| inf_lt_left.2 hxw⟩ ≤
        μ.max ⟨x ⊓ y, x, inf_lt_left.2 hxy⟩ :=
      A_le_max_inf μ hxy (huxw.trans (inf_le_inf_left x hy.1))
    _ ≤ μ.max ⟨y, x ⊔ w, hy.2⟩ :=
      hμcvx.max_inf_le_max hxI hyI hxy (sup_le le_sup_left hy.2.le)

/-! ### Convexity of `μ.max` -/

/-- `μ.max` inherits convexity from `μ`. -/
lemma IsConvexOn.max (hμcvx : μ.IsConvexOn I) : (μ.max).IsConvexOn I :=
  ⟨fun _ _ hxI hyI hxy ↦ hμcvx.max_inf_le_max hxI hyI hxy le_rfl⟩

/-- Applying `max` twice gives the same value as applying it once on an interval where
`μ` is convex. -/
lemma IsConvexOn.max_max (hμcvx : μ.IsConvexOn I) : μ.max.max I = μ.max I := by
  apply eq_of_le_of_ge
  · refine max_le fun v hv ↦ ?_
    simpa only [inf_eq_right.2 hv.1.le] using
      hμcvx.max_inf_le_max ⟨hv.1.le, hv.2⟩ I.left_mem (not_le_of_gt hv.1)
        ((sup_eq_left.2 hv.1.le).symm ▸ hv.2)
  · exact le_max ⟨I.lt, le_rfl⟩

/-- Replacing `μ` by `μ.max` does not change the value when A moves first on intervals
on which `μ` is convex. -/
lemma IsConvexOn.A_max (hμcvx : μ.IsConvexOn I) : μ.max.A I = μ.A I := by
  have key : ∀ a, I.left ≤ a → ∀ h : a < I.right,
      μ.max.max ⟨a, I.right, h⟩ = μ.max ⟨a, I.right, h⟩ :=
    fun a ha h ↦ (hμcvx.mono (I₂ := ⟨a, I.right, h⟩) ⟨ha, le_rfl⟩).max_max
  apply eq_of_le_of_ge
  · exact le_A fun a ha ↦ (A_le ha).trans (key a ha.1 ha.2).le
  · exact le_A fun a ha ↦ (A_le ha).trans (key a ha.1 ha.2).ge

/-! ### Game values along a chain -/

/-- For a payoff function convex on `I` and `x < y < z` in `I`, the `μ.A`-value on `(x, z)`
dominates the meet of the values on the two subintervals cut at `y`. -/
lemma IsConvexOn.inf_le_A (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z) :
    μ.A ⟨x, y, h₁⟩ ⊓ μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, z, h₁.trans h₂⟩ := by
  refine le_A fun a ha ↦ ?_
  by_cases hya : y ≤ a
  · calc
      μ.A ⟨x, y, h₁⟩ ⊓ μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨y, z, h₂⟩ := inf_le_right
      _ ≤ μ.max ⟨a, z, ha.2⟩ := A_le (I := ⟨y, z, h₂⟩) ⟨hya, ha.2⟩
  · calc
      μ.A ⟨x, y, h₁⟩ ⊓ μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, y, h₁⟩ := inf_le_left
      _ ≤ μ.max ⟨y ⊓ a, y, inf_lt_left.2 hya⟩ :=
        A_le_max_inf μ hya (le_inf h₁.le ha.1)
      _ ≤ μ.max ⟨a, z, ha.2⟩ :=
        hμcvx.max_inf_le_max hyI ⟨hxI.1.trans ha.1, ha.2.le.trans hzI.2⟩ hya
          (sup_le h₂.le ha.2.le)

/-- For a payoff function convex on `I` and `x < y < z` in `I`, if the `μ.A`-value on `(x, y)`
dominates that on `(y, z)`, then `μ.A (y, z) = μ.A (x, z)`. -/
lemma IsConvexOn.A_eq_of_ge (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z)
    (h' : μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, y, h₁⟩) :
    μ.A ⟨y, z, h₂⟩ = μ.A ⟨x, z, h₁.trans h₂⟩ :=
  le_antisymm (le_trans (le_inf h' le_rfl) <| hμcvx.inf_le_A hxI hyI hzI h₁ h₂)
    (A_anti_left μ h₁ h₂)

/-- For a payoff function convex on `I` and `x < y < z` in `I`, if the `μ.A`-value on `(x, y)`
is strictly below that on `(y, z)`, then it bounds the value on `(x, z)` from below. -/
lemma IsConvexOn.A_le_A_of_lt (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z)
    (h' : μ.A ⟨x, y, h₁⟩ < μ.A ⟨y, z, h₂⟩) :
    μ.A ⟨x, y, h₁⟩ ≤ μ.A ⟨x, z, h₁.trans h₂⟩ :=
  le_trans (le_inf le_rfl h'.le) <| hμcvx.inf_le_A hxI hyI hzI h₁ h₂

/-- For a payoff function convex on `I` and `x < y < z` in `I`, either
`μ.A (x, z) = μ.A (y, z)` or `μ.A (x, y) ≤ μ.A (x, z) < μ.A (y, z)`, provided the two
subinterval values are comparable or the infimum defining `μ.A (x, z)` is attained. -/
lemma IsConvexOn.A_eq_or_lt (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z)
    (h' : Relation.SymmGen (· ≤ ·) (μ.A ⟨x, y, h₁⟩) (μ.A ⟨y, z, h₂⟩) ∨
      μ.IsAttained ⟨x, z, h₁.trans h₂⟩) :
    μ.A ⟨y, z, h₂⟩ = μ.A ⟨x, z, h₁.trans h₂⟩ ∨
      (μ.A ⟨x, y, h₁⟩ ≤ μ.A ⟨x, z, h₁.trans h₂⟩ ∧
        μ.A ⟨x, z, h₁.trans h₂⟩ < μ.A ⟨y, z, h₂⟩) := by
  rcases h' with hc | hatt
  · by_cases h₃ : μ.A ⟨y, z, h₂⟩ = μ.A ⟨x, z, h₁.trans h₂⟩
    · exact Or.inl h₃
    · have hne : ¬ μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, y, h₁⟩ :=
        fun hle ↦ h₃ (hμcvx.A_eq_of_ge hxI hyI hzI h₁ h₂ hle)
      exact Or.inr ⟨hμcvx.A_le_A_of_lt hxI hyI hzI h₁ h₂
          (lt_of_le_not_ge (hc.resolve_right hne) hne),
        (A_anti_left μ h₁ h₂).lt_of_ne' h₃⟩
  · rcases hatt with ⟨a, ha, hres⟩
    refine or_iff_not_imp_left.2 fun hnot ↦ ?_
    have hya : ¬ y ≤ a := fun hcontra ↦ hnot <|
      le_antisymm (hres ▸ A_le (I := ⟨y, z, h₂⟩) ⟨hcontra, ha.2⟩) (A_anti_left μ h₁ h₂)
    exact ⟨hres ▸ (le_trans (A_le_max_inf μ hya (le_inf h₁.le ha.1)) <|
        hμcvx.max_inf_le_max hyI ⟨le_trans hxI.1 ha.1, le_trans ha.2.le hzI.2⟩ hya
          (sup_le h₂.le ha.2.le)),
      (A_anti_left μ h₁ h₂).lt_of_ne' hnot⟩

/-- For a convex payoff function with values in a complete linear order, a strict improvement
of the `μ.A`-value on a proper initial segment forces the value on the complementary segment
to equal the global value. -/
lemma IsConvex.A_right_eq_of_A_left_gt {S : Type*} [CompleteLinearOrder S]
    [Nontrivial ℒ] [BoundedOrder ℒ] {μ : PayoffFunction ℒ S}
    (hμcvx : μ.IsConvex) {x : ℒ} (h₁ : ⊥ < x) (h₂ : x < ⊤)
    (h' : μ.A ⊤ < μ.A ⟨⊥, x, h₁⟩) :
    μ.A ⟨x, ⊤, h₂⟩ = μ.A ⊤ :=
  ((isConvexOn_top_iff.2 hμcvx).A_eq_or_lt (StrictIntvl.mem_top ⊥) (StrictIntvl.mem_top x)
      (StrictIntvl.mem_top ⊤) h₁ h₂ (Or.inl <| le_total _ _)).resolve_right
    fun h₃ ↦ not_le_of_gt h' h₃.1

/-! ### Game values along a join -/

private lemma IsConvexOn.A_le_max_or (hμcvx : μ.IsConvexOn I) {x y u w : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (h₁ : u < x) (h₂ : u < y)
    (hwI : w ∈ I) (hw₁ : u ≤ w) (hw₂ : w < x ⊔ y) :
    μ.A ⟨u, x, h₁⟩ ≤ μ.max ⟨w, x ⊔ y, hw₂⟩ ∨ μ.A ⟨u, y, h₂⟩ ≤ μ.max ⟨w, x ⊔ y, hw₂⟩ := by
  rcases not_and_or.1 (fun hc ↦ not_le_of_gt hw₂ (sup_le hc.1 hc.2)) with hx | hy
  · exact Or.inl <| le_trans (A_le_max_inf μ hx (le_inf h₁.le hw₁)) <|
      hμcvx.max_inf_le_max hxI hwI hx (sup_le le_sup_left hw₂.le)
  · exact Or.inr <| le_trans (A_le_max_inf μ hy (le_inf h₂.le hw₁)) <|
      hμcvx.max_inf_le_max hyI hwI hy (sup_le le_sup_right hw₂.le)

/-- For a payoff function convex on `I` and `u, x, y ∈ I` with `u < x` and `u < y`, the
`μ.A`-value on `(u, x ⊔ y)` dominates the meet of the values on `(u, x)` and `(u, y)`. -/
lemma IsConvexOn.inf_A_le_A_sup (hμcvx : μ.IsConvexOn I) {x y u : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (huI : u ∈ I) (h₁ : u < x) (h₂ : u < y) :
    μ.A ⟨u, x, h₁⟩ ⊓ μ.A ⟨u, y, h₂⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left h₁⟩ :=
  le_A fun _ hw ↦ (hμcvx.A_le_max_or hxI hyI h₁ h₂
      ⟨le_trans huI.1 hw.1, le_trans hw.2.le <| sup_le hxI.2 hyI.2⟩ hw.1 hw.2).elim
    (le_trans inf_le_left) (le_trans inf_le_right)

/-- For a payoff function convex on `I` and `u, x, y ∈ I` with `u < x` and `u < y`, the
`μ.A`-value on `(u, x ⊔ y)` dominates one of the values on `(u, x)` and `(u, y)`, provided
those values are comparable or the infimum defining `μ.A (u, x ⊔ y)` is attained. -/
lemma IsConvexOn.A_le_A_sup_or (hμcvx : μ.IsConvexOn I) {x y u : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (huI : u ∈ I) (h₁ : u < x) (h₂ : u < y)
    (hcpb : Relation.SymmGen (· ≤ ·) (μ.A ⟨u, x, h₁⟩) (μ.A ⟨u, y, h₂⟩) ∨
      μ.IsAttained ⟨u, x ⊔ y, lt_sup_of_lt_left h₁⟩) :
    μ.A ⟨u, x, h₁⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left h₁⟩ ∨
      μ.A ⟨u, y, h₂⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left h₁⟩ := by
  rcases hcpb with hc | hatt
  · rcases hc with h₃ | h₄
    · exact Or.inl <| le_trans (le_inf le_rfl h₃) <| hμcvx.inf_A_le_A_sup hxI hyI huI h₁ h₂
    · exact Or.inr <| le_trans (le_inf h₄ le_rfl) <| hμcvx.inf_A_le_A_sup hxI hyI huI h₁ h₂
  · rcases hatt with ⟨a, ha, ha''⟩
    exact ha'' ▸ hμcvx.A_le_max_or hxI hyI h₁ h₂
      ⟨le_trans huI.1 ha.1, le_trans ha.2.le <| sup_le hxI.2 hyI.2⟩ ha.1 ha.2

end PayoffFunction

end HarderNarasimhan
