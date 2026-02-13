/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Interval
import HarderNarasimhan.Semistability.Impl

/-!
This file provides “translation” lemmas between the global notion `Semistable μ` and
the interval-indexed version `semistableI μ I`.

These are re-exports of internal equivalences proved in
`HarderNarasimhan.Semistability.Impl`, but they are kept in a separate file because
they form part of the public API and are frequently used to move between:

* global semistability (on the whole lattice), and
* semistability of a restriction `Resμ I μ` to a sub-interval.
-/

namespace HarderNarasimhan

/--
Global semistability is equivalent to semistability on the total interval `TotIntvl`.
This is mostly a normalization lemma: many internal arguments are phrased using the
interval-indexed predicates, while user-facing statements prefer `Semistable μ`.

API note: this theorem is the recommended bridge between the “global” and “interval” APIs.
-/
theorem semistable_iff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
  Semistable μ ↔ semistableI μ TotIntvl
------------
:= impl.semistable_iff μ

/--
Semistability on an interval is equivalent to global semistability of the restriction.
This is the key transport lemma: it lets one turn an interval-local hypothesis into a
global `Semistable` hypothesis on `Resμ I μ`, and conversely.

API note: this is the primary transport lemma for switching between `semistableI` and
`Semistable (Resμ I μ)`.
-/
theorem semistableI_iff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) :
------------
semistableI μ I ↔ Semistable (Resμ I μ)
------------
:= impl.semistableI_iff μ I

end HarderNarasimhan
