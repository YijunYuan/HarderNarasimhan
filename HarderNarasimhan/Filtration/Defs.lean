/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Semistable.Breakpoints
public import Mathlib.Data.Rel
public import Mathlib.Order.RelSeries

/-!
# Harder–Narasimhan filtrations

A Harder–Narasimhan filtration of a payoff function `μ` is a finite chain
`⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤` with semistable successive intervals. Writing `aᵢ`
for the value of `μ.A` on the `i`-th interval, we require `¬ aᵢ ≤ aᵢ₊₁`.
For a linearly ordered codomain, this says that the values strictly decrease.

Existence is proved in `HarderNarasimhan/Filtration/Exists.lean`, and uniqueness for a
linearly ordered codomain is proved in `HarderNarasimhan/Filtration/Unique.lean`.

## Main definitions

* `HarderNarasimhan.PayoffFunction.Admissible`: the codomain order is total, or the infima
  defining `μ.A` are attained. This is a hypothesis of the existence theorem.
* `HarderNarasimhan.PayoffFunction.HarderNarasimhanFiltration`: a Harder–Narasimhan filtration.
* `HarderNarasimhan.PayoffFunction.semistableRel`: the relation defined by strict intervals
  on which the restricted payoff function is semistable.

## Implementation notes

Filtrations are indexed by `ℕ` and extended constantly by `⊤` from `F.length` onwards.
The length is determined by the underlying function: it is the first index at which the
filtration reaches `⊤`. Thus equality of filtrations is pointwise equality.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Admissible

variable [Preorder ℒ] [CompleteLattice S]

/-- A payoff function is admissible if its codomain order is total or the infimum defining
`μ.A I` is attained for every strict interval `I`.

Together with convexity, the descending chain condition on `μ.A`, and well-foundedness
of `>` on the lattice, this ensures the existence of greatest breakpoints. Every payoff
function with a complete linearly ordered codomain is admissible. -/
class Admissible (μ : PayoffFunction ℒ S) : Prop where
  /-- Either `≤` is total on the codomain, or every defining infimum of `μ.A` is attained. -/
  total_or_attained : Std.Total (· ≤ · : S → S → Prop) ∨ ∀ I : StrictIntvl ℒ, μ.IsAttained I

end Admissible

section AdmissibleLinearOrder

variable [Preorder ℒ] [CompleteLinearOrder S]

/-- Over a complete linear order every payoff function is admissible, since `≤` is total. -/
instance (μ : PayoffFunction ℒ S) : μ.Admissible where
  total_or_attained := Or.inl inferInstance

end AdmissibleLinearOrder

section HarderNarasimhanFiltration

variable [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]

/-- A Harder–Narasimhan filtration of `μ` is a finite strictly increasing chain from `⊥`
to `⊤` with semistable successive intervals, whose successive `μ.A`-values satisfy
`¬ aᵢ ≤ aᵢ₊₁`. For a linearly ordered codomain, these values strictly decrease.

The chain is indexed by `ℕ` and is constantly `⊤` from `length` onwards. -/
structure HarderNarasimhanFiltration (μ : PayoffFunction ℒ S) where
  /-- The underlying chain. -/
  toFun : ℕ → ℒ
  /-- The number of strict steps in the chain. -/
  length : ℕ
  /-- The chain is monotone. -/
  monotone : Monotone toFun
  /-- The chain starts at `⊥`. -/
  head_eq_bot : toFun 0 = ⊥
  /-- The chain reaches `⊤` at index `length`. -/
  length_eq_top : toFun length = ⊤
  /-- The chain is strictly increasing up to `length`. -/
  strictMonoOn : StrictMonoOn toFun (Set.Iic length)
  /-- Each successive step `(F i, F (i + 1))` is semistable. -/
  piecewise_isSemistable : ∀ i, (hi : i < length) →
    (μ.restrict ⟨toFun i, toFun (i + 1), strictMonoOn hi.le hi (lt_add_one i)⟩).IsSemistable
  /-- No `μ.A`-value of a step is less than or equal to that of the next step. -/
  not_A_le_succ : ∀ i, (hi : i + 1 < length) →
    ¬ μ.A ⟨toFun i, toFun (i + 1),
        strictMonoOn (Nat.le_of_succ_le hi.le) hi.le (lt_add_one i)⟩ ≤
      μ.A ⟨toFun (i + 1), toFun (i + 2), strictMonoOn hi.le hi (lt_add_one (i + 1))⟩

namespace HarderNarasimhanFiltration

variable {μ : PayoffFunction ℒ S}

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
    cases F
    cases G
    dsimp only at h hlen
    subst h
    subst hlen
    rfl

@[simp] lemma toFun_eq_coe (F : μ.HarderNarasimhanFiltration) : F.toFun = ⇑F := rfl

variable {F G : μ.HarderNarasimhanFiltration} {m : ℕ}

/-- Below `F.length` the chain has not yet reached `⊤`. -/
lemma ne_top_of_lt (h : m < F.length) : F m ≠ ⊤ := fun hc ↦
  (F.strictMonoOn h.le (Set.mem_Iic.2 le_rfl) h).ne (hc.trans F.length_eq_top.symm)

/-- The length is the least index at which the filtration reaches `⊤`. -/
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_top_of_lt hc h

/-- From `F.length` onwards, the chain is constantly `⊤`. -/
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ :=
  top_le_iff.1 <| F.length_eq_top ▸ F.monotone h

/-- A term differs from `⊤` if and only if its index is less than the length. -/
lemma ne_top_iff_lt_length : F m ≠ ⊤ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_top_of_length_le hc), ne_top_of_lt⟩

/-- Each term below `⊤` is strictly less than its successor. -/
lemma lt_succ_of_ne_top (h : F m ≠ ⊤) : F m < F (m + 1) := by
  have hm : m < F.length := ne_top_iff_lt_length.1 h
  exact F.strictMonoOn hm.le hm (lt_add_one m)

/-- Two Harder–Narasimhan filtrations are equal if they agree at every index. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end HarderNarasimhanFiltration

end HarderNarasimhanFiltration

section SemistableRel

variable [PartialOrder ℒ] [CompleteLattice S]

/-- The relation between `x < y` for which the restriction of `μ` to the interval with
endpoints `x` and `y` is semistable. -/
def semistableRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : x < y, (μ.restrict ⟨x, y, h⟩).IsSemistable}

variable {μ : PayoffFunction ℒ S}

/-- A series of semistable intervals is strictly increasing. -/
lemma relSeries_strictMono (s : RelSeries μ.semistableRel) : StrictMono s.toFun :=
  LTSeries.strictMono (s.map ⟨id, fun h ↦ h.choose⟩)

open Fin.NatCast in
/-- Consecutive terms of a semistable series are strictly increasing, with natural-number
indices cast to `Fin`. -/
lemma relSeries_step_lt (s : RelSeries μ.semistableRel) {i : ℕ} (hi : i + 1 < s.length) :
    s.toFun ↑i < s.toFun ↑(i + 1) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi.le (lt_add_one i))

open Fin.NatCast in
/-- The terms at indices `i + 1` and `i + 2` of a semistable series are strictly increasing. -/
lemma relSeries_succ_step_lt (s : RelSeries μ.semistableRel) {i : ℕ}
    (hi : i + 1 < s.length) : s.toFun ↑(i + 1) < s.toFun ↑(i + 2) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi (lt_add_one (i + 1)))

end SemistableRel

end PayoffFunction

end HarderNarasimhan
