/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Restrict

/-!
# Convexity — definitions

Definition 2.3 of *Harder–Narasimhan Games*, its interval form, and the affine condition
of Remark 4.26. The basic conversions here support the implementations in `Convexity.Impl`.
Numbered statements from §2.2 are collected in `Convexity.Results`.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [CompleteLattice S]

/-! ### The convexity typeclasses -/

/--
Definition 2.3. A payoff function is convex if `μ (x ⊓ y, x) ≤ μ (y, x ⊔ y)` whenever `¬ x ≤ y`.
The latter condition ensures that both intervals are strict.
-/
class IsConvex (μ : PayoffFunction ℒ S) : Prop where
  /-- Definition 2.3: the convexity inequality. -/
  le : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/--
Definition 2.3, localized to an interval. A payoff function is convex on `I` if the convexity
inequality holds for every `x, y ∈ I` with `¬ x ≤ y`.
-/
class IsConvexOn (μ : PayoffFunction ℒ S) (I : StrictIntvl ℒ) : Prop where
  /-- Definition 2.3: the convexity inequality, for pairs in `I`. -/
  le : ∀ x y : ℒ, x ∈ I → y ∈ I → (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ ≤ μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

variable {μ : PayoffFunction ℒ S} {I : StrictIntvl ℒ}

/--
Auxiliary restriction property for Definition 2.3. Convexity on an interval implies convexity on
each subinterval.
-/
lemma IsConvexOn.mono {I₁ I₂ : StrictIntvl ℒ} (h : μ.IsConvexOn I₁) (hI : I₂ ≤ I₁) :
    μ.IsConvexOn I₂ :=
  ⟨fun x y hx hy hxy ↦ h.le x y ⟨le_trans hI.1 hx.1, le_trans hx.2 hI.2⟩
    ⟨le_trans hI.1 hy.1, le_trans hy.2 hI.2⟩ hxy⟩

section Top

variable [Nontrivial ℒ] [BoundedOrder ℒ]

/--
Auxiliary total-interval characterization for Definition 2.3. Convexity on the total interval
`⊤` is the same as global convexity.
-/
@[simp] lemma isConvexOn_top_iff : μ.IsConvexOn ⊤ ↔ μ.IsConvex :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.le x y (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxy⟩,
    fun h ↦ ⟨fun x y _ _ hxy ↦ h.le x y hxy⟩⟩

/-- Auxiliary instance for Definition 2.3: convexity on the total interval. -/
instance [μ.IsConvex] : μ.IsConvexOn ⊤ := isConvexOn_top_iff.mpr inferInstance

/-- Auxiliary instance for Definition 2.3: global convexity from the total interval. -/
instance [μ.IsConvexOn ⊤] : μ.IsConvex := isConvexOn_top_iff.mp inferInstance

end Top

/--
Auxiliary restriction characterization for Definition 2.3. Convexity on `I` is equivalent to
convexity of the restriction to the points of `I`.
-/
theorem isConvexOn_iff_isConvex_restrict : μ.IsConvexOn I ↔ (μ.restrict I).IsConvex :=
  ⟨fun h ↦ ⟨fun x y hxy ↦ h.le x y x.prop y.prop hxy⟩,
    fun h ↦ ⟨fun x y hx hy hxy ↦ h.le ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩⟩

/--
Remark 4.26 (affine payoff functions). A payoff function is affine if `μ (x ⊓ y, x) = μ (y, x ⊔
y)` whenever `¬ x ≤ y`.
-/
class IsAffine (μ : PayoffFunction ℒ S) : Prop where
  /-- Remark 4.26: the affine equality. -/
  eq : ∀ x y : ℒ, (h : ¬ x ≤ y) →
    μ ⟨x ⊓ y, x, inf_lt_left.2 h⟩ = μ ⟨y, x ⊔ y, right_lt_sup.2 h⟩

/--
Auxiliary implication from Remark 4.26 to Definition 2.3. An affine payoff function is convex.
-/
instance IsAffine.toIsConvex [haff : μ.IsAffine] : μ.IsConvex :=
  ⟨fun x y hxy ↦ (haff.eq x y hxy).le⟩

/-- Auxiliary restriction instance for Remark 4.26. Restriction preserves the affine property. -/
instance [haff : μ.IsAffine] : (μ.restrict I).IsAffine :=
  ⟨fun x y h ↦ haff.eq x y h⟩

/-- Auxiliary form of Definition 2.3: global convexity implies convexity on every interval. -/
lemma IsConvex.isConvexOn (h : μ.IsConvex) (J : StrictIntvl ℒ) : μ.IsConvexOn J :=
  ⟨fun x y _ _ hxy ↦ h.le x y hxy⟩

end PayoffFunction

end HarderNarasimhan
