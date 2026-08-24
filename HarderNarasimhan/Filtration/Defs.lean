/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Semistability.Results
import Mathlib.Order.RelSeries
import Mathlib.Data.Rel

/-!
Definitions for Harder–Narasimhan filtrations.

This module introduces:

* `μAdmissible μ`: a mild hypothesis ensuring that the “stable breakpoint” machinery
  from semistability can be iterated (either because the codomain order is total, or
  because `μ` attains its relevant suprema),
* `HarderNarasimhanFiltration μ`: the record packaging a finite increasing chain
  from `⊥` to `⊤` whose successive subquotients are semistable and whose `μA`-slopes
  satisfy a strict anti-monotonicity condition, and
* `IntervalSemistableRel μ`: the relation on `ℒ` used to view a filtration as a
  `RelSeries` in later developments.

The actual construction of the canonical filtration is carried out in
`HarderNarasimhan.Filtration.Impl`.

API overview:

* Import this file for the core types `μAdmissible`, `HarderNarasimhanFiltration`, and the
  relation `IntervalSemistableRel` used to view filtrations as `RelSeries`.
* Import `HarderNarasimhan.Filtration.Results` for the canonical inhabitant/uniqueness statements
  and for the “ready-to-use” `RelSeries` packaging.
-/

namespace HarderNarasimhan

/--
Admissibility hypothesis for building Harder–Narasimhan filtrations.
If your codomain `S` is a complete linear order, you typically get `μAdmissible μ` for free.

We allow two common ways to ensure the “maximal stable element exists” steps needed
in the construction:

* `S` has a total order (`Std.Total (· ≤ ·)`), or
* for every interval `I`, the `μ`-values relevant to `IsAttained μ I` are achieved.

This is phrased as a typeclass so later theorems can assume it implicitly.

API note: this is the main extra hypothesis needed for the existence theorem.
-/
class μAdmissible {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) : Prop where
  μ_adm : (Std.Total (· ≤ · : S → S → Prop)) ∨ ∀ I : Intvl ℒ,  IsAttained μ I

/--
In a complete linear order, admissibility is automatic.

This instance uses the fact that linearity implies totality of `≤`.
-/
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : Intvl ℒ → S} :
μAdmissible μ where
  μ_adm := Or.inl Std.instTotalLeOfIsLinearPreorder

open Classical in
/--
A Harder–Narasimhan filtration as a finite increasing chain.
For the canonical inhabitant and uniqueness theorems, prefer importing
`HarderNarasimhan.Filtration.Results`.

Fields:

* `filtration : ℕ → ℒ` is the underlying chain.
* `monotone`, `first_eq_bot`, `fin_len` enforce that it starts at `⊥` and eventually
  reaches `⊤`.
* `strict_mono` provides strictness up to the (chosen) finite length.
* `piecewise_semistable` asserts that each successive interval is semistable.
* `μA_pseudo_strict_anti` encodes the strict decrease condition on successive
  `μA`-slopes (the “HN slopes are strictly decreasing” property).

The filtration is expressed using restrictions `Resμ` to successive intervals.

API note: this structure is the central user-facing object of the filtration layer.
-/
@[ext]
structure HarderNarasimhanFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) where
  filtration : ℕ → ℒ
  monotone             : Monotone filtration
  first_eq_bot         : filtration 0 = ⊥
  fin_len              : ∃ n : ℕ, filtration n = ⊤
  strict_mono          : StrictMonoOn filtration (Set.Iic (Nat.find fin_len))
  piecewise_semistable : ∀ i : ℕ, (h: i < Nat.find (fin_len)) →
    Semistable (Resμ ⟨filtration i, filtration (i+1), strict_mono h.le h (lt_add_one i)⟩ μ)
  μA_pseudo_strict_anti: ∀ i : ℕ, (hi : i + 1 < Nat.find fin_len) →
    ¬ μA μ ⟨filtration i, filtration (i+1),
        strict_mono (Nat.le_of_succ_le hi.le) hi.le (lt_add_one i)⟩ ≤
    μA μ ⟨filtration (i+1), filtration (i+2), strict_mono hi.le hi (Nat.lt_add_one (i + 1))⟩


namespace HarderNarasimhanFiltration

variable {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
  {S : Type*} [CompleteLattice S] {μ : Intvl ℒ → S}

open Classical in
/--
The length of a Harder–Narasimhan filtration: the first index at which it reaches `⊤`.

All `Nat.find`-based bookkeeping about the chain length is encapsulated here and in the
accompanying lemmas; downstream code should use `F.length` and never touch `Nat.find` directly.
-/
noncomputable def length (F : HarderNarasimhanFiltration μ) : ℕ := Nat.find F.fin_len

open Classical in
@[simp] lemma filtration_length (F : HarderNarasimhanFiltration μ) :
    F.filtration F.length = ⊤ := Nat.find_spec F.fin_len

open Classical in
lemma ne_top_of_lt_length (F : HarderNarasimhanFiltration μ) {m : ℕ} (h : m < F.length) :
    F.filtration m ≠ ⊤ := Nat.find_min F.fin_len h

open Classical in
lemma length_le_of_eq_top (F : HarderNarasimhanFiltration μ) {m : ℕ}
    (h : F.filtration m = ⊤) : F.length ≤ m := Nat.find_min' F.fin_len h

end HarderNarasimhanFiltration

/-- The relation “there is a semistable interval from `x` to `y`”.
  This is a `SetRel ℒ ℒ` so that a filtration can be interpreted as a `RelSeries` whose
  successor steps certify semistability of each interval.

  API note: this relation is intended for consumers who prefer `RelSeries` packaging.
-/
def IntervalSemistableRel {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
: SetRel ℒ ℒ :=
{(x, y) | ∃ h : x < y, Semistable (Resμ ⟨x, y, h⟩ μ)}
end HarderNarasimhan
