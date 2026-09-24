/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Semistability.Defs
public import Mathlib.Data.Rel
public import Mathlib.Order.RelSeries

/-!
# Section 3.3: definitions of Harder–Narasimhan filtrations

Definition 3.9 supplies the filtration data and admissibility hypothesis.
The chain is indexed by natural numbers and extended constantly by `⊤` after its length.
`Impl` constructs the canonical filtration and proves uniqueness; `Results` states the
paper-facing existence and uniqueness results.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Admissible

variable [Preorder ℒ] [CompleteLattice S]

/-- Section 3.3, hypothesis (c) preceding Definition 3.9, packaged as an auxiliary typeclass.
A payoff function is admissible if its codomain order is total or the infimum defining
`μ.A I` is attained for every strict interval `I`.

Together with convexity, the descending chain condition on `μ.A`, and well-foundedness
of `>` on the lattice, this ensures the existence of greatest breakpoints. Every payoff
function with a complete linearly ordered codomain is admissible. -/
class Admissible (μ : PayoffFunction ℒ S) : Prop where
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  Either `≤` is total on the codomain, or every defining infimum of `μ.A` is attained. -/
  total_or_attained : Std.Total (· ≤ · : S → S → Prop) ∨ ∀ I : StrictIntvl ℒ, μ.IsAttained I

end Admissible

section AdmissibleLinearOrder

variable [Preorder ℒ] [CompleteLinearOrder S]

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
Over a complete linear order every payoff function is admissible, since `≤` is total. -/
instance (μ : PayoffFunction ℒ S) : μ.Admissible where
  total_or_attained := Or.inl inferInstance

end AdmissibleLinearOrder

section HarderNarasimhanFiltration

variable [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- Definition 3.9 and Theorem 3.10: the defining properties of a Harder–Narasimhan filtration.
A Harder–Narasimhan filtration of `μ` is a finite strictly increasing chain from `⊥`
to `⊤` with semistable successive intervals, whose successive `μ.A`-values satisfy
`¬ aᵢ ≤ aᵢ₊₁`. For a linearly ordered codomain, these values strictly decrease.

The chain is indexed by `ℕ` and is constantly `⊤` from `length` onwards. -/
structure HarderNarasimhanFiltration (μ : PayoffFunction ℒ S) where
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The underlying chain. -/
  toFun : ℕ → ℒ
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The number of strict steps in the chain. -/
  length : ℕ
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The chain is monotone. -/
  monotone : Monotone toFun
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The chain starts at `⊥`. -/
  head_eq_bot : toFun 0 = ⊥
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The chain reaches `⊤` at index `length`. -/
  length_eq_top : toFun length = ⊤
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  The chain is strictly increasing up to `length`. -/
  strictMonoOn : StrictMonoOn toFun (Set.Iic length)
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  Each successive step `(F i, F (i + 1))` is semistable. -/
  piecewise_isSemistable : ∀ i, (hi : i < length) →
    (μ.restrict ⟨toFun i, toFun (i + 1), strictMonoOn hi.le hi (lt_add_one i)⟩).IsSemistable
  /-- Auxiliary API for Definition 3.9 and Theorem 3.10.
  No `μ.A`-value of a step is less than or equal to that of the next step. -/
  not_A_le_succ : ∀ i, (hi : i + 1 < length) →
    ¬ μ.A ⟨toFun i, toFun (i + 1),
        strictMonoOn (Nat.le_of_succ_le hi.le) hi.le (lt_add_one i)⟩ ≤
      μ.A ⟨toFun (i + 1), toFun (i + 2), strictMonoOn hi.le hi (lt_add_one (i + 1))⟩

namespace HarderNarasimhanFiltration

variable {μ : PayoffFunction ℒ S}

/-- Auxiliary coercion for Definition 3.9: a filtration is determined by its chain. -/
instance : FunLike (μ.HarderNarasimhanFiltration) ℕ ℒ where
  coe := toFun
  coe_injective := by
    have key : ∀ F G : μ.HarderNarasimhanFiltration, F.toFun = G.toFun →
        F.length ≤ G.length := by
      intro F G h
      by_contra hc
      rw [not_le] at hc
      have h1 := F.strictMonoOn hc.le (Set.mem_Iic.2 le_rfl) hc
      rw [F.length_eq_top, h, G.length_eq_top] at h1
      exact lt_irrefl ⊤ h1
    intro F G h
    have hlen : F.length = G.length := le_antisymm (key F G h) (key G F h.symm)
    cases F; cases G
    dsimp only at h hlen
    subst h; subst hlen
    rfl

/-- Auxiliary API for Definition 3.9: the coercion agrees with the underlying chain. -/
@[simp] lemma toFun_eq_coe (F : μ.HarderNarasimhanFiltration) : F.toFun = ⇑F := rfl

variable {F G : μ.HarderNarasimhanFiltration} {m : ℕ}

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
Below `F.length` the chain has not yet reached `⊤`. -/
lemma ne_top_of_lt (h : m < F.length) : F m ≠ ⊤ := fun hc ↦
  (F.strictMonoOn h.le (Set.mem_Iic.2 le_rfl) h).ne (hc.trans F.length_eq_top.symm)

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
The length is the least index at which the filtration reaches `⊤`. -/
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_top_of_lt hc h

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
From `F.length` onwards, the chain is constantly `⊤`. -/
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ :=
  top_le_iff.1 <| F.length_eq_top ▸ F.monotone h

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
A term differs from `⊤` if and only if its index is less than the length. -/
lemma ne_top_iff_lt_length : F m ≠ ⊤ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_top_of_length_le hc), ne_top_of_lt⟩

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
Each term below `⊤` is strictly less than its successor. -/
lemma lt_succ_of_ne_top (h : F m ≠ ⊤) : F m < F (m + 1) := by
  have hm : m < F.length := ne_top_iff_lt_length.1 h
  exact F.strictMonoOn hm.le hm (lt_add_one m)

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
Two Harder–Narasimhan filtrations are equal if they agree at every index. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end HarderNarasimhanFiltration

end HarderNarasimhanFiltration

section SemistableRel

variable [PartialOrder ℒ] [CompleteLattice S]

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
The relation between `x < y` for which the restriction of `μ` to the interval with
endpoints `x` and `y` is semistable. -/
def semistableRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : x < y, (μ.restrict ⟨x, y, h⟩).IsSemistable}

variable {μ : PayoffFunction ℒ S}

/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
A series of semistable intervals is strictly increasing. -/
lemma relSeries_strictMono (s : RelSeries μ.semistableRel) : StrictMono s.toFun :=
  LTSeries.strictMono (s.map ⟨id, fun h ↦ h.choose⟩)

open Fin.NatCast in
/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
Consecutive terms of a semistable series are strictly increasing, with natural-number
indices cast to `Fin`. -/
lemma relSeries_step_lt (s : RelSeries μ.semistableRel) {i : ℕ} (hi : i + 1 < s.length) :
    s.toFun ↑i < s.toFun ↑(i + 1) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi.le (lt_add_one i))

open Fin.NatCast in
/-- Auxiliary API for Definition 3.9 and Theorem 3.10.
The terms at indices `i + 1` and `i + 2` of a semistable series are strictly increasing. -/
lemma relSeries_succ_step_lt (s : RelSeries μ.semistableRel) {i : ℕ}
    (hi : i + 1 < s.length) : s.toFun ↑(i + 1) < s.toFun ↑(i + 2) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi (lt_add_one (i + 1)))

end SemistableRel

end PayoffFunction

end HarderNarasimhan
