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

This file introduces the convexity assumptions on a payoff function `μ` over a lattice `ℒ`
and derives the fundamental inequalities they impose on the extremal operations `μ.max` and
`μ.A`.

Convexity compares the payoffs of the two “opposite” subintervals determined by a
non-comparable pair `x, y`: the lower-left interval `(x ⊓ y, x)` and the upper-right interval
`(y, x ⊔ y)`.  It comes in a global form `IsConvex` and an interval-local form `IsConvexOn`,
related by `isConvexOn_top_iff` and `isConvexOn_iff_isConvex_restrict`; the local form is
antitone in the interval (`IsConvexOn.mono`).  The strengthening `IsAffine`, which requires
equality of the two payoffs, implies convexity.

## Main definitions

* `PayoffFunction.IsConvex`, `PayoffFunction.IsConvexOn` : the convexity typeclasses.
* `PayoffFunction.IsAffine` : the affine strengthening (equality instead of `≤`).

## Main results

* `IsConvexOn.max_inf_le_max`, `IsConvexOn.A_le_A_sup` : the fundamental inequality chain.
* `IsConvexOn.max`, `IsConvexOn.max_max`, `IsConvexOn.A_max` : `μ.max` inherits convexity,
  is idempotent, and leaves `μ.A` unchanged.
* `IsConvexOn.inf_le_A`, `IsConvexOn.A_eq_of_ge`, `IsConvexOn.A_le_A_of_lt`,
  `IsConvexOn.A_eq_or_lt` : comparison of `μ.A` along a chain `x < y < z`.
* `IsConvexOn.inf_A_le_A_sup`, `IsConvexOn.A_le_A_sup_or` : comparison of `μ.A` along a join
  `x ⊔ y`.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [CompleteLattice S]

/-! ### The convexity typeclasses -/

/-- A payoff function `μ` on a lattice is *convex* if for every non-comparable pair
`¬ x ≤ y` the payoff of the lower-left interval `(x ⊓ y, x)` is at most the payoff of the
upper-right interval `(y, x ⊔ y)`.  This is a lattice-theoretic analogue of discrete
convexity/supermodularity inequalities. -/
class IsConvex (μ : PayoffFunction ℒ S) : Prop where
  /-- The convexity inequality. -/
  le : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/-- The interval-local convexity condition: the inequality of `IsConvex` is only required for
pairs `x, y` lying in a fixed strict interval `I`.  This form is used when restricting to
subintervals; see `IsConvexOn.mono` and `isConvexOn_iff_isConvex_restrict`. -/
class IsConvexOn (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop where
  /-- The convexity inequality, for pairs in `I`. -/
  le : ∀ x y : ℒ, x ∈ I → y ∈ I → (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/-- Interval-local convexity is antitone in the interval: convexity on a larger interval
implies convexity on any subinterval. -/
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

/-- Convexity on an interval `I` is the same as global convexity of the restriction
`μ.restrict I`.  This enables rewriting convexity hypotheses when switching between an
interval in `ℒ` and its points type `↥I`. -/
theorem isConvexOn_iff_isConvex_restrict : μ.IsConvexOn I ↔ (μ.restrict I).IsConvex :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.le x y x.prop y.prop hxy⟩,
    fun h ↦ ⟨fun x y hx hy hxy ↦ h.le ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩⟩

/-- A payoff function is *affine* if the two payoffs compared by convexity are equal:
`μ (x ⊓ y, x) = μ (y, x ⊔ y)` for every non-comparable pair.  This expresses compatibility
of `μ` with the lattice operations and strengthens `IsConvex`. -/
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

/-! ### The fundamental inequality chain

Convexity propagates bounds from lower-left subintervals to upper-right ones. -/

/-- For `u ≤ x ⊓ w` the first-player value on `(u, x)` is bounded by `μ.max (x ⊓ w, x)`.
This is a formal consequence of the definition of `μ.A` and needs no convexity. -/
lemma A_le_max_inf (μ : PayoffFunction ℒ S) {x w u : ℒ} (hxw : ¬ x ≤ w) (huxw : u ≤ x ⊓ w) :
    μ.A ⟨u, x, lt_of_le_of_lt huxw (inf_lt_left.2 hxw)⟩ ≤
      μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ :=
  A_le ⟨huxw, inf_lt_left.2 hxw⟩

/-- Under convexity on `I`, the `μ.max`-value of the lower-left interval `(x ⊓ w, x)` is
bounded by the `μ.max`-value of any interval `(w, t)` with `x ⊔ w ≤ t`. -/
lemma IsConvexOn.max_inf_le_max (hμcvx : μ.IsConvexOn I) {x w t : ℒ}
    (hxI : x ∈ I) (hwI : w ∈ I) (hxw : ¬ x ≤ w) (hxwt : x ⊔ w ≤ t) :
    μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ ≤
      μ.max ⟨w, t, lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩ := by
  refine max_le fun b hb ↦ ?_
  have hh : x ⊓ w = b ⊓ w :=
    le_antisymm (le_inf hb.1.le inf_le_right) (inf_le_inf_right w hb.2)
  have hbnlew : ¬ b ≤ w := inf_lt_left.mp (hh ▸ hb.1)
  simp only [hh]
  exact le_trans (hμcvx.le b w ⟨le_of_lt (lt_of_le_of_lt (le_inf hxI.1 hwI.1) hb.1),
    le_trans hb.2 hxI.2⟩ hwI hbnlew) <|
    le_max (I := ⟨w, t, lt_of_le_of_lt' hxwt <| right_lt_sup.2 hxw⟩)
      ⟨right_lt_sup.2 hbnlew, le_trans (sup_le_sup_right hb.2 w) hxwt⟩

/-- Under convexity on `I`, the first-player value on `(u, x)` with `u ≤ x ⊓ w` is bounded by
the first-player value on `(w, x ⊔ w)`. -/
lemma IsConvexOn.A_le_A_sup (hμcvx : μ.IsConvexOn I) {x w u : ℒ}
    (hxI : x ∈ I) (hwI : w ∈ I) (hxw : ¬ x ≤ w) (huxw : u ≤ x ⊓ w) :
    μ.A ⟨u, x, lt_of_le_of_lt huxw <| inf_lt_left.2 hxw⟩ ≤
      μ.A ⟨w, x ⊔ w, right_lt_sup.2 hxw⟩ := by
  refine le_A fun y hy ↦ ?_
  have h₁ : ¬ x ≤ y := fun h ↦ lt_irrefl (x ⊔ w) <| lt_of_le_of_lt (sup_le_sup_right h w) <|
    (sup_eq_left.2 hy.1).symm ▸ hy.2
  exact le_trans (A_le_max_inf μ h₁ <| le_trans huxw <| inf_le_inf_left x hy.1) <|
    hμcvx.max_inf_le_max hxI ⟨le_trans hwI.1 hy.1, le_trans hy.2.le <| sup_le hxI.2 hwI.2⟩
      h₁ (sup_le le_sup_left hy.2.le)

/-! ### Stability of the extremal operations under convexity

`μ.max` inherits convexity, is idempotent, and does not change the first-player value. -/

/-- `μ.max` inherits convexity from `μ`. -/
lemma IsConvexOn.max (hμcvx : μ.IsConvexOn I) : (μ.max).IsConvexOn I :=
  ⟨fun _ _ hxI hyI hxy ↦ hμcvx.max_inf_le_max hxI hyI hxy le_rfl⟩

/-- `μ.max` is idempotent on intervals on which `μ` is convex. -/
lemma IsConvexOn.max_max (hμcvx : μ.IsConvexOn I) : μ.max.max I = μ.max I := by
  apply eq_of_le_of_ge
  · refine max_le fun v hv ↦ ?_
    simpa only [inf_eq_right.2 hv.1.le] using
      hμcvx.max_inf_le_max ⟨hv.1.le, hv.2⟩ I.left_mem (not_le_of_gt hv.1)
        ((sup_eq_left.2 hv.1.le).symm ▸ hv.2)
  · exact le_max ⟨I.lt, le_rfl⟩

/-- Replacing `μ` by `μ.max` does not change the first-player value on intervals on which `μ`
is convex. -/
lemma IsConvexOn.A_max (hμcvx : μ.IsConvexOn I) : μ.max.A I = μ.A I := by
  have key : ∀ a, I.left ≤ a → ∀ h : a < I.right,
      μ.max.max ⟨a, I.right, h⟩ = μ.max ⟨a, I.right, h⟩ :=
    fun a ha h ↦ (hμcvx.mono (I₂ := ⟨a, I.right, h⟩) ⟨ha, le_rfl⟩).max_max
  apply eq_of_le_of_ge
  · exact le_A fun a ha ↦ (A_le ha).trans (key a ha.1 ha.2).le
  · exact le_A fun a ha ↦ (A_le ha).trans (key a ha.1 ha.2).ge

/-! ### `μ.A` along a chain

How the first-player value behaves when an interval is cut at an intermediate point; the
convexity-free monotonicity statement is `PayoffFunction.A_anti_left`. -/

/-- Under convexity on `I`, the first-player value on `(x, z)` dominates the meet of the
values on the two subintervals cut at `y`. -/
lemma IsConvexOn.inf_le_A (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z) :
    μ.A ⟨x, y, h₁⟩ ⊓ μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, z, h₁.trans h₂⟩ := by
  refine le_A fun a ha ↦ ?_
  by_cases hya : y ≤ a
  · exact le_trans inf_le_right <| A_le (I := ⟨y, z, h₂⟩) ⟨hya, ha.2⟩
  · exact le_trans inf_le_left <| le_trans (A_le_max_inf μ hya (le_inf h₁.le ha.1)) <|
      hμcvx.max_inf_le_max hyI ⟨le_trans hxI.1 ha.1, le_trans ha.2.le hzI.2⟩ hya
        (sup_le h₂.le ha.2.le)

/-- If the first-player value on `(x, y)` dominates the one on `(y, z)`, then cutting at `y`
does not change the value: `μ.A (y, z) = μ.A (x, z)`. -/
lemma IsConvexOn.A_eq_of_ge (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z)
    (h' : μ.A ⟨y, z, h₂⟩ ≤ μ.A ⟨x, y, h₁⟩) :
    μ.A ⟨y, z, h₂⟩ = μ.A ⟨x, z, h₁.trans h₂⟩ :=
  le_antisymm (le_trans (le_inf h' le_rfl) <| hμcvx.inf_le_A hxI hyI hzI h₁ h₂)
    (A_anti_left μ h₁ h₂)

/-- If the first-player value on `(x, y)` is strictly below the one on `(y, z)`, then it
bounds the value on `(x, z)` from below. -/
lemma IsConvexOn.A_le_A_of_lt (hμcvx : μ.IsConvexOn I) {x y z : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (hzI : z ∈ I) (h₁ : x < y) (h₂ : y < z)
    (h' : μ.A ⟨x, y, h₁⟩ < μ.A ⟨y, z, h₂⟩) :
    μ.A ⟨x, y, h₁⟩ ≤ μ.A ⟨x, z, h₁.trans h₂⟩ :=
  le_trans (le_inf le_rfl h'.le) <| hμcvx.inf_le_A hxI hyI hzI h₁ h₂

/-- Dichotomy for `μ.A` along a chain `x < y < z`: assuming either comparability of the two
subinterval values or attainment on `(x, z)`, cutting at `y` either leaves the value
unchanged, or the value on `(x, z)` lies strictly between the two subinterval values. -/
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

/-- In a complete linear order, a strict improvement of the first-player value on the left
initial segment forces the value on the complementary segment to equal the global value. -/
lemma IsConvex.A_right_eq_of_A_left_gt {S : Type*} [CompleteLinearOrder S]
    [Nontrivial ℒ] [BoundedOrder ℒ] {μ : PayoffFunction ℒ S}
    (hμcvx : μ.IsConvex) {x : ℒ} (h₁ : ⊥ < x) (h₂ : x < ⊤)
    (h' : μ.A ⊤ < μ.A ⟨⊥, x, h₁⟩) :
    μ.A ⟨x, ⊤, h₂⟩ = μ.A ⊤ :=
  ((isConvexOn_top_iff.2 hμcvx).A_eq_or_lt (StrictIntvl.mem_top ⊥) (StrictIntvl.mem_top x)
      (StrictIntvl.mem_top ⊤) h₁ h₂ (Or.inl <| le_total _ _)).resolve_right
    fun h₃ ↦ not_le_of_gt h' h₃.1

/-! ### `μ.A` along a join

How the first-player value on `(u, x ⊔ y)` compares with the values on `(u, x)` and
`(u, y)`. -/

private lemma IsConvexOn.A_le_max_or (hμcvx : μ.IsConvexOn I) {x y u w : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (h₁ : u < x) (h₂ : u < y)
    (hwI : w ∈ I) (hw₁ : u ≤ w) (hw₂ : w < x ⊔ y) :
    μ.A ⟨u, x, h₁⟩ ≤ μ.max ⟨w, x ⊔ y, hw₂⟩ ∨ μ.A ⟨u, y, h₂⟩ ≤ μ.max ⟨w, x ⊔ y, hw₂⟩ := by
  rcases not_and_or.1 (fun hc ↦ not_le_of_gt hw₂ (sup_le hc.1 hc.2)) with hx | hy
  · exact Or.inl <| le_trans (A_le_max_inf μ hx (le_inf h₁.le hw₁)) <|
      hμcvx.max_inf_le_max hxI hwI hx (sup_le le_sup_left hw₂.le)
  · exact Or.inr <| le_trans (A_le_max_inf μ hy (le_inf h₂.le hw₁)) <|
      hμcvx.max_inf_le_max hyI hwI hy (sup_le le_sup_right hw₂.le)

/-- Under convexity on `I`, the first-player value on `(u, x ⊔ y)` dominates the meet of the
values on `(u, x)` and `(u, y)`. -/
lemma IsConvexOn.inf_A_le_A_sup (hμcvx : μ.IsConvexOn I) {x y u : ℒ}
    (hxI : x ∈ I) (hyI : y ∈ I) (huI : u ∈ I) (h₁ : u < x) (h₂ : u < y) :
    μ.A ⟨u, x, h₁⟩ ⊓ μ.A ⟨u, y, h₂⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left h₁⟩ :=
  le_A fun _ hw ↦ (hμcvx.A_le_max_or hxI hyI h₁ h₂
      ⟨le_trans huI.1 hw.1, le_trans hw.2.le <| sup_le hxI.2 hyI.2⟩ hw.1 hw.2).elim
    (le_trans inf_le_left) (le_trans inf_le_right)

/-- Under convexity on `I` and a comparability or attainment hypothesis, the first-player
value on `(u, x ⊔ y)` dominates one of the two values on `(u, x)` and `(u, y)`. -/
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
