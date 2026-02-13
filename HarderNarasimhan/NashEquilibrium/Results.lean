import HarderNarasimhan.NashEquilibrium.Impl

/-!
# Nash equilibrium: public statements

This file re-exports the main lemmas and propositions about Nash equilibria for the
Harder–Narasimhan game, stated in a user-facing way.

The proofs live in `HarderNarasimhan.NashEquilibrium.Impl` under the `impl` namespace.

API overview:

* Import this file to use the public lemmas (`remark_4_10`, `proposition_4_11`, …) without
  depending on internal implementation details.
* The core predicate is `NashEquilibrium μ`, defined in `HarderNarasimhan.NashEquilibrium.Defs`.
-/

namespace HarderNarasimhan

/--
Basic bounds: `μmin ≤ μ ≤ μmax` on any interval.

This is Remark 4.10 (preliminary inequality) in the development.
-/
lemma μmin_lt_μ_lt_μmax {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) :
∀ I : {p : ℒ × ℒ // p.1 < p.2}, μmin μ I ≤ μ I ∧ μ I ≤ μmax μ I
:= impl.rmk4d10₀ μ


/-
Remark 4.10: equivalent formulations of the key inequality and Nash equilibrium.
It packages the key comparison inequality `μBstar ≤ μAstar` and its two one-sided variants.

API note: this lemma is a convenient gateway for proving/using `NashEquilibrium μ`.
-/
lemma remark_4_10 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
(
  μBstar μ ≤ μAstar μ ↔ ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) →
    μmin μ ⟨(⊥,y),hy⟩ ≤ μmax μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx⟩
) ∧
(
  WeakAscendingChainCondition μ → WeakSlopeLike₁ μ →
  (
    NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊥) →
      μmin μ ⟨(⊥,y),bot_lt_iff_ne_bot.2 hy⟩ ≤ μmin μ TotIntvl
  )
) ∧ (
  StrongDescendingChainCondition μ → WeakSlopeLike₂ μ →
  (
    NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊤) →
      μmax μ TotIntvl ≤ μmax μ ⟨(y,⊤),lt_top_iff_ne_top.2 hy⟩
  )
)
:= ⟨impl.rmk4d10₁ μ,⟨impl.rmk4d10₂ μ,impl.rmk4d10₃ μ⟩⟩


/--
Proposition 4.11: relating `μmin μ TotIntvl = μmax μ TotIntvl` and the inequality `μBstar ≤ μAstar`.
-/
lemma proposition_4_11 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
(
  μmin μ TotIntvl = μmax μ TotIntvl → μBstar μ ≤ μAstar μ
) ∧ (
  WeakAscendingChainCondition μ → WeakSlopeLike₁ μ →
  StrongDescendingChainCondition μ → WeakSlopeLike₂ μ →
  μBstar μ ≤ μAstar μ → μmin μ TotIntvl = μmax μ TotIntvl
)
:= ⟨impl.prop4d11₁ μ,impl.prop4d11₂ μ⟩


/--
Proposition 4.12: an implication `μmax TotIntvl = μ TotIntvl → μmin TotIntvl = μmax TotIntvl`
under a local “gap” condition.
-/
lemma proposition_4_12 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨
  μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
μmax μ TotIntvl = μ TotIntvl → μmin μ TotIntvl = μmax μ TotIntvl
:= impl.prop4d12 μ h


/--
Remark 4.13: `SlopeLike` provides the “gap” condition used in Proposition 4.12.
-/
lemma remark_4_13 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ) :
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
  ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨
    μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩
:= impl.rmk4d13 μ hμ


/--
Proposition 4.14: a dual implication `μmin TotIntvl = μ TotIntvl → μmax TotIntvl = μmin TotIntvl`
under the dual local condition.
-/
lemma proposition_4_14 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
  μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨
  ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
μmin μ TotIntvl = μ TotIntvl → μmax μ TotIntvl = μmin μ TotIntvl
:= impl.prop4d14 μ h


/--
Remark 4.15: `SlopeLike` provides the dual local condition used in Proposition 4.14.
-/
lemma remark_4_15 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ) :
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) →
  μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨
  ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩
:= impl.rmk4d15 μ hμ


/--
Proposition 4.16: a `TFAE` package relating the three equalities for `μmin/μmax` on `TotIntvl`,
and (under chain conditions) equivalence with Nash equilibrium.
-/
lemma proposition_4_16 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ) :
(
  List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl
  ]
) ∧ (
  WeakAscendingChainCondition μ → StrongDescendingChainCondition μ →
  List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl,
  NashEquilibrium μ
  ]
)
:= by
  refine ⟨impl.prop4d16₁ μ hμ,fun h₁ h₂ ↦ ?_⟩
  tfae_have 1 ↔ 2 := ((impl.prop4d16₁ μ hμ).out 0 1 (by norm_num) (by norm_num))
  tfae_have 2 ↔ 3 := ((impl.prop4d16₁ μ hμ).out 1 2 (by norm_num) (by norm_num))
  tfae_have 3 ↔ 4 := impl.prop4d16₂ μ hμ h₁ h₂
  tfae_finish


/--
Proposition 4.18: under semistability, we always have `μBstar ≤ μAstar`, and a Nash equilibrium
follows from either one-sided hypothesis package.
-/
lemma proposition_4_18 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : Semistable μ) :
(
  μBstar μ ≤ μAstar μ
) ∧ (
  (WeakAscendingChainCondition μ ∧ WeakSlopeLike₁ μ) ∨
  (StrongDescendingChainCondition μ ∧ WeakSlopeLike₂ μ) →
    NashEquilibrium μ
)
:= ⟨impl.prop4d18₁ μ hμ,impl.prop4d18₂ μ hμ⟩


/--
Proposition 4.20: Nash equilibrium implies semistability, assuming the one-sided hypotheses on all
initial restrictions.
-/
lemma proposition_4_20 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) →
  WeakAscendingChainCondition (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ))
(h₂ :  ∀ x : ℒ, (hx : x ≠ ⊥) →
  WeakSlopeLike₁ (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ)) :
NashEquilibrium μ → Semistable μ
:= impl.prop4d20 μ h₁ h₂


/-
Theorem 4.21: a `TFAE` package for Nash equilibrium and the `μmin/μmax` equalities.
It characterizes `NashEquilibrium μ` in terms of the equalities among `μmin`/`μmax` on `TotIntvl`.

API note: this is the main user-facing equivalence statement of the Nash-equilibrium chapter.
-/
theorem NashEquil_equiv {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) [hμ : SlopeLike μ]
[h₁ : WeakAscendingChainCondition μ] [h₂ : StrongDescendingChainCondition μ] :
List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl,
  NashEquilibrium μ
  ]
∧ (
  Semistable μ → NashEquilibrium μ
) ∧ (
  (∀ x : ℒ, (hx : x ≠ ⊥) → WeakAscendingChainCondition (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ)) →
  NashEquilibrium μ → Semistable μ
)
:= impl.thm4d21 μ hμ h₁ h₂

end HarderNarasimhan
