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

This file defines the Harder–Narasimhan filtrations of a payoff function
`μ : PayoffFunction ℒ S`: finite chains `⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤` whose successive
steps are semistable and whose `μ.A`-slopes strictly decrease.  The canonical construction of
such a filtration is `μ.hnFiltration` in `HarderNarasimhan.Filtration.Exists`; its uniqueness
over a complete linear order is proved in `HarderNarasimhan.Filtration.Unique`.

The length of the chain is stored as a `length` field, but it carries no extra information:
it is provably the least index at which the chain reaches `⊤` (`length_le_of_eq_top`), hence
it is determined by the chain itself; accordingly extensionality (`ext`) only requires the
underlying functions to agree.

The side condition `PayoffFunction.Admissible` records the two standard hypotheses under
which the greatest-breakpoint machinery of
`HarderNarasimhan.PayoffFunction.Semistable.Breakpoints` can be iterated: either the codomain
order is total, or all the infima defining `μ.A` are attained.

Finally, `μ.semistableRel` is the relation "`x < y` and the game on `(x, y)` is semistable",
which lets a Harder–Narasimhan filtration be repackaged as a `RelSeries`; see
`exists_relSeries_semistableRel` in `HarderNarasimhan.Filtration.Unique`.

## Main definitions

* `PayoffFunction.Admissible` : the codomain order is total, or `μ` attains the infima
  defining `μ.A`.
* `PayoffFunction.HarderNarasimhanFiltration` : the structure packaging a Harder–Narasimhan
  filtration for `μ`, applied to indices via the `FunLike` coercion.
* `PayoffFunction.semistableRel` : the semistable-interval relation on `ℒ` used for the
  `RelSeries` packaging.

## Main results

* `HarderNarasimhanFiltration.length_le_of_eq_top`, `ne_top_of_lt`, `eq_top_of_length_le` :
  the `length` field is the least index at which the chain reaches `⊤`.
* `HarderNarasimhanFiltration.ext` : two filtrations with the same underlying chain are
  equal.

## References

* [Huayi Chen & Marion Jeannin, *Harder–Narasimhan Games*][ChenJeannin]
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*}

section Admissible

variable [Preorder ℒ] [CompleteLattice S]

/-- A payoff function is *admissible* when the greatest-breakpoint machinery behind the
construction of Harder–Narasimhan filtrations can be iterated: either the order on the
codomain `S` is total, or the infimum defining `μ.A I` is attained on every interval `I`.
Over a complete linear order admissibility is automatic. -/
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

/-- A **Harder–Narasimhan filtration** for the payoff function `μ`: a finite chain
`⊥ = F 0 < F 1 < ⋯ < F F.length = ⊤`, extended constantly by `⊤` above `length`, whose
successive steps are semistable and whose `μ.A`-slopes strictly decrease.

`length` is stored as data but carries no extra information: it is provably the *least*
index at which the chain reaches `⊤` (`length_le_of_eq_top`), hence determined by `toFun`;
accordingly `ext` only asks for `toFun` to agree. -/
structure HarderNarasimhanFiltration (μ : PayoffFunction ℒ S) where
  /-- The underlying chain; apply via the coercion, `F n`. -/
  toFun : ℕ → ℒ
  /-- The index at which the chain reaches `⊤`. -/
  length : ℕ
  /-- The chain is monotone (constantly `⊤` above `length`). -/
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
  /-- Successive `μ.A`-slopes strictly decrease, in the `¬ · ≤ ·` sense appropriate for a
  possibly non-linear codomain `S`. -/
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

/-- Minimality of the `length` field: it is the least index at which the chain reaches
`⊤`.  In particular `length` is determined by the underlying chain. -/
lemma length_le_of_eq_top (h : F m = ⊤) : F.length ≤ m :=
  not_lt.1 fun hc ↦ ne_top_of_lt hc h

/-- Above `F.length` the chain is constantly `⊤`. -/
lemma eq_top_of_length_le (h : F.length ≤ m) : F m = ⊤ :=
  top_le_iff.1 <| F.length_eq_top ▸ F.monotone h

/-- The chain has reached `⊤` at an index iff the index is at least `F.length`. -/
lemma ne_top_iff_lt_length : F m ≠ ⊤ ↔ m < F.length :=
  ⟨fun h ↦ not_le.1 fun hc ↦ h (eq_top_of_length_le hc), ne_top_of_lt⟩

/-- One-step strict growth of the chain before it reaches `⊤`. -/
lemma lt_succ_of_ne_top (h : F m ≠ ⊤) : F m < F (m + 1) := by
  have hm : m < F.length := ne_top_iff_lt_length.1 h
  exact F.strictMonoOn hm.le hm (lt_add_one m)

/-- Two Harder–Narasimhan filtrations with the same underlying chain are equal: the
`length` field is determined by the chain (`length_le_of_eq_top`) and the remaining fields
are proofs. -/
@[ext] theorem ext (h : ∀ n, F n = G n) : F = G := DFunLike.ext F G h

end HarderNarasimhanFiltration

end HarderNarasimhanFiltration

section SemistableRel

variable [PartialOrder ℒ] [CompleteLattice S]

/-- The relation "`x < y` and the game on the interval `(x, y)` is semistable".  A
Harder–Narasimhan filtration is precisely a `RelSeries` for this relation from `⊥` to `⊤`
whose `μ.A`-slopes strictly decrease; see `exists_relSeries_semistableRel`. -/
def semistableRel (μ : PayoffFunction ℒ S) : SetRel ℒ ℒ :=
  {(x, y) | ∃ h : x < y, (μ.restrict ⟨x, y, h⟩).IsSemistable}

variable {μ : PayoffFunction ℒ S}

/-- The underlying function of a `RelSeries` for `μ.semistableRel` is strictly monotone,
obtained by forgetting the semistability witnesses. -/
lemma relSeries_strictMono (s : RelSeries μ.semistableRel) : StrictMono s.toFun :=
  LTSeries.strictMono (s.map ⟨id, fun h ↦ h.choose⟩)

open Fin.NatCast in
/-- Consecutive elements of a `RelSeries` for `μ.semistableRel` are strictly increasing,
expressed via `ℕ`-indexed casts so that slope conditions can be stated with indices `i`,
`i + 1`, `i + 2`. -/
lemma relSeries_step_lt (s : RelSeries μ.semistableRel) {i : ℕ} (hi : i + 1 < s.length) :
    s.toFun ↑i < s.toFun ↑(i + 1) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi.le (lt_add_one i))

open Fin.NatCast in
/-- The strict inequality of `relSeries_step_lt`, shifted by one. -/
lemma relSeries_succ_step_lt (s : RelSeries μ.semistableRel) {i : ℕ}
    (hi : i + 1 < s.length) : s.toFun ↑(i + 1) < s.toFun ↑(i + 2) :=
  relSeries_strictMono s (Fin.natCast_strictMono hi (lt_add_one (i + 1)))

end SemistableRel

end PayoffFunction

end HarderNarasimhan
