/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Convexity.Impl

/-!
# Convexity — numbered statements

The statements of §2.2 of *Harder–Narasimhan Games*. Definitions are in `Convexity.Defs`;
the interval-local proofs are in `Convexity.Impl`.
-/

@[expose] public section

namespace HarderNarasimhan

open PayoffFunction Impl.PayoffFunction

variable {ℒ S : Type*} [Lattice ℒ] [Nontrivial ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable (μ : PayoffFunction ℒ S)

/-- Lemma 2.4: the comparison inequalities (2.2) and (2.3). -/
lemma lemma_2_4 (hμ : μ.IsConvex) {x w u t : ℒ} (hxw : ¬ x ≤ w)
    (hu : u ≤ x ⊓ w) (ht : x ⊔ w ≤ t) :
    (μ.A ⟨u, x, hu.trans_lt (inf_lt_left.2 hxw)⟩ ≤
        μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ ∧
      μ.max ⟨x ⊓ w, x, inf_lt_left.2 hxw⟩ ≤
        μ.max ⟨w, t, (right_lt_sup.2 hxw).trans_le ht⟩) ∧
    μ.A ⟨u, x, hu.trans_lt (inf_lt_left.2 hxw)⟩ ≤ μ.A ⟨w, x ⊔ w, right_lt_sup.2 hxw⟩ :=
  ⟨⟨A_le_max_inf μ hxw hu,
      IsConvexOn.max_inf_le_max (hμ.isConvexOn ⊤)
        (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxw ht⟩,
    IsConvexOn.A_le_A_sup (hμ.isConvexOn ⊤) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxw hu⟩

/-- Remark 2.5: convexity of `μ.max`, idempotence, and invariance of Alice's value. -/
lemma remark_2_5 (hμ : μ.IsConvex) :
    μ.max.IsConvex ∧ ∀ I : StrictIntvl ℒ, μ.max.max I = μ.max I ∧ μ.max.A I = μ.A I :=
  ⟨isConvexOn_top_iff.mp (IsConvexOn.max (hμ.isConvexOn ⊤)),
    fun I ↦ ⟨IsConvexOn.max_max (hμ.isConvexOn I), IsConvexOn.A_max (hμ.isConvexOn I)⟩⟩

/-- Proposition 2.6: (2.4) and the three comparisons along a chain `x < y < z`. -/
lemma proposition_2_6 {x y z : ℒ} (hxy : x < y) (hyz : y < z) :
    μ.A ⟨x, z, hxy.trans hyz⟩ ≤ μ.A ⟨y, z, hyz⟩ ∧
    (μ.IsConvex →
      μ.A ⟨x, y, hxy⟩ ⊓ μ.A ⟨y, z, hyz⟩ ≤ μ.A ⟨x, z, hxy.trans hyz⟩ ∧
      (μ.A ⟨y, z, hyz⟩ ≤ μ.A ⟨x, y, hxy⟩ →
        μ.A ⟨y, z, hyz⟩ = μ.A ⟨x, z, hxy.trans hyz⟩) ∧
      (μ.A ⟨x, y, hxy⟩ < μ.A ⟨y, z, hyz⟩ →
        μ.A ⟨x, y, hxy⟩ ≤ μ.A ⟨x, z, hxy.trans hyz⟩ ∧
          μ.A ⟨x, z, hxy.trans hyz⟩ ≤ μ.A ⟨y, z, hyz⟩) ∧
      (Relation.SymmGen (· ≤ ·) (μ.A ⟨x, y, hxy⟩) (μ.A ⟨y, z, hyz⟩) ∨
          μ.IsAttained ⟨x, z, hxy.trans hyz⟩ →
        μ.A ⟨y, z, hyz⟩ = μ.A ⟨x, z, hxy.trans hyz⟩ ∨
          (μ.A ⟨x, y, hxy⟩ ≤ μ.A ⟨x, z, hxy.trans hyz⟩ ∧
            μ.A ⟨x, z, hxy.trans hyz⟩ < μ.A ⟨y, z, hyz⟩))) :=
  ⟨A_anti_left μ hxy hyz, fun hμ ↦
    let h := hμ.isConvexOn ⊤
    ⟨IsConvexOn.inf_le_A h
        (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxy hyz,
      IsConvexOn.A_eq_of_ge h
        (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hxy hyz,
      fun hlt ↦ ⟨IsConvexOn.A_le_A_of_lt h (StrictIntvl.mem_top _) (StrictIntvl.mem_top _)
        (StrictIntvl.mem_top _) hxy hyz hlt, A_anti_left μ hxy hyz⟩,
      IsConvexOn.A_eq_or_lt h (StrictIntvl.mem_top _) (StrictIntvl.mem_top _)
        (StrictIntvl.mem_top _) hxy hyz⟩⟩

/-- Remark 2.7: a strict improvement on an initial segment preserves the complementary value. -/
lemma remark_2_7 {S : Type*} [CompleteLinearOrder S] (μ : PayoffFunction ℒ S)
    (hμ : μ.IsConvex) {x : ℒ} (hx : ⊥ < x) (hx' : x < ⊤)
    (h : μ.A ⊤ < μ.A ⟨⊥, x, hx⟩) : μ.A ⟨x, ⊤, hx'⟩ = μ.A ⊤ :=
  IsConvex.A_right_eq_of_A_left_gt hμ hx hx' h

/-- Proposition 2.8: the value on a join dominates the meet, or one comparable/attained value. -/
lemma proposition_2_8 (hμ : μ.IsConvex) {u x y : ℒ} (hx : u < x) (hy : u < y) :
    μ.A ⟨u, x, hx⟩ ⊓ μ.A ⟨u, y, hy⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left hx⟩ ∧
    (Relation.SymmGen (· ≤ ·) (μ.A ⟨u, x, hx⟩) (μ.A ⟨u, y, hy⟩) ∨
        μ.IsAttained ⟨u, x ⊔ y, lt_sup_of_lt_left hx⟩ →
      μ.A ⟨u, x, hx⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left hx⟩ ∨
        μ.A ⟨u, y, hy⟩ ≤ μ.A ⟨u, x ⊔ y, lt_sup_of_lt_left hx⟩) :=
  ⟨IsConvexOn.inf_A_le_A_sup (hμ.isConvexOn ⊤)
      (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hx hy,
    IsConvexOn.A_le_A_sup_or (hμ.isConvexOn ⊤)
      (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) (StrictIntvl.mem_top _) hx hy⟩

end HarderNarasimhan
