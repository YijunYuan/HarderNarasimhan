/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Defs

/-!
# Section 4.4: Nash equilibrium — definition

The unnumbered definition at the beginning of Section 4.4, preceding Notation 4.9.
-/

@[expose] public section

namespace HarderNarasimhan

namespace PayoffFunction

variable {ℒ S : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] [CompleteLattice S]
variable {μ : PayoffFunction ℒ S}

/-- Section 4.4 (definition preceding Notation 4.9). The Harder–Narasimhan games have a Nash
equilibrium if the values obtained when A and B move first are equal. This condition concerns
equality of values; attainment is a separate property. -/
class HasNashEquilibrium (μ : PayoffFunction ℒ S) : Prop where
  /-- Section 4.4 (definition preceding Notation 4.9): the two game values coincide. -/
  eq : μ.A ⊤ = μ.B ⊤

end PayoffFunction

end HarderNarasimhan
