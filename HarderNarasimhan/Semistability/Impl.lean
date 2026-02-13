/-
Copyright (c) 2025-2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl
import HarderNarasimhan.Semistability.Defs
import Mathlib.Tactic.Linarith

/-!
This file contains implementation lemmas for the semistability module.

Semistability in this project is formulated in terms of the extremal invariant `μA` (from
`Basic.lean`) and the
selection predicates `S₁I`/`S₂I` (from `Semistability/Defs.lean`). The results in this file build
the internal machinery needed to:
- prove a descending chain condition for `μA` from simpler hypotheses,
- construct a nonempty set `StI μ I` of “stable breakpoints” inside an interval,
- show uniqueness and comparison properties of such breakpoints under additional hypotheses,
- relate the interval-local notion `semistableI` to the global typeclass `Semistable`, and
- transport semistability along restriction (`Resμ`).

As an `Impl.lean` file, many names mirror the numbering of the accompanying paper (e.g. `prop3d4`),
and are primarily intended for internal reuse; most users should import
`HarderNarasimhan.Semistability.Results`.
-/

namespace HarderNarasimhan

namespace impl

/-
Internal namespace containing proof-engineering lemmas for semistability.

The objects here are designed to be composable building blocks for the public-facing theorems.
-/

/-
Proposition 3.2 (interval-local form): monotonicity of `μA` under enlarging the right endpoint,
in the special case where `μA (x,z) = ⊤`.

Assuming convexity on `I`, if `x<z` and `μA (x,z)` is top, then for any `a<x` in the interval,
we have `μA (a,x) ≤ μA (a,z)`.

API note: this lemma is used to derive a descending chain condition by contradiction.
-/
lemma prop3d2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI I μ)
(x : ℒ) (hxI : InIntvl I x)
(z : ℒ) (hzI : InIntvl I z)
(h : x < z)
(h' : μA μ ⟨(x, z), h⟩ = ⊤)
(a : ℒ) (haI : InIntvl I a) (hax : a < x) :
μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩ := by
  have h'' : μA μ ⟨(a , x) , hax⟩ ⊓ μA μ ⟨(x , z) , h⟩ ≤ μA μ ⟨(a,z),lt_trans hax h⟩ :=
    impl.prop2d6₁I I μ hμcvx a haI x hxI z hzI ⟨hax,h⟩
  rwa [h', inf_top_eq] at h''


/-
Corollary 3.3: a convenient sufficient condition for the DCC on `μA`.

Given a hypothesis that any strict descending chain `f` eventually produces an interval
`(f(N+1), f(N))` with `μA = ⊤`, we deduce the class `μA_DescendingChainCondition μ`.

API note: this turns a “top occurs along chains” assumption into the formal DCC typeclass.
-/
lemma cor3d3 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : ConvexI TotIntvl μ)
(h : ∀ f : ℕ → ℒ, (h : StrictAnti f) →  ∃N : ℕ, μA μ ⟨(f <| N + 1, f N),h (lt_add_one N)⟩ = ⊤)
: μA_DescendingChainCondition μ := by
  refine { μ_dcc := fun a f h₁ h₂ ↦ ?_ }
  rcases (h f h₂) with ⟨N, hN⟩
  use N
  have := prop3d2 TotIntvl μ hμcvx (f <| N + 1) (in_TotIntvl <| f <| N + 1) (f N)
    (in_TotIntvl <| f N) (h₂ (lt_add_one N)) hN a (in_TotIntvl <| a) (h₁ <| N + 1)
  exact not_lt_of_ge this


/-
Auxiliary set `ℒₛ μ I x`: candidates that strictly improve the `μA`-value.

 Given a current breakpoint candidate `x` (as a subtype element of `I`), this set consists of
 `p ∈ ℒ` such that:
- `p` lies in `I`,
- `p` is not the left endpoint and lies strictly below `x`, and
- `μA (I.left, p)` is strictly greater than `μA (I.left, x)`.

This set is used to define an iterative process that searches for better breakpoints.
-/
def ℒₛ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : {p : ℒ // InIntvl I p}) (hx : I.val.1 ≠ x) : Set ℒ :=
{p : ℒ | ∃ h₁ : InIntvl I p, ∃ h₂ : I.val.1 ≠ p ∧ p < x,
  μA μ ⟨(I.val.1,p),lt_of_le_of_ne h₁.1 h₂.1⟩ >
  μA μ ⟨(I.val.1 , x.val) , lt_of_le_of_ne x.prop.1 hx⟩}


/-
Core recursive construction used in Proposition 3.4.

`prop3d4₀func μ I k` produces a point of the interval `I` (as a subtype `{p // InIntvl I p}`) by
iterating:
- start at the right endpoint for `k=0`,
- if the previous point is the left endpoint, stay there,
- otherwise, if there is a “strictly improving” point in `ℒₛ`, pick a minimal such point using
  well-foundedness,
- if there is no improvement, jump to the left endpoint.

API note: the definition is noncomputable due to classical choice and well-founded `has_min`.
-/
noncomputable def prop3d4₀func
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [h : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(k : ℕ) : {p : ℒ // InIntvl I p} :=
  letI := Classical.propDecidable
  match k with
  | 0 => ⟨I.val.2, ⟨le_of_lt I.prop, le_rfl⟩⟩
  | n+1 =>
    let prev := prop3d4₀func μ I n
    if hbot : I.val.1 = prev.val then
      ⟨I.val.1, ⟨le_rfl,le_of_lt I.prop⟩⟩
    else
      if hne : (ℒₛ μ I prev hbot).Nonempty then
        let res := h.wf.has_min (ℒₛ μ I prev hbot) hne
        ⟨(res).choose,res.choose_spec.1.out.choose⟩
      else
        ⟨I.val.1, ⟨le_rfl,le_of_lt I.prop⟩⟩


/-
Helper lemma: if step `i+1` is not at the left endpoint, then step `i` is also not at the left
endpoint.

This is used repeatedly to justify that the “improvement set” `ℒₛ` is well-defined at earlier steps.
-/
lemma prop3d4₀func_helper {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i + 1)).val) :
I.val.1 ≠ (prop3d4₀func μ I i).val := by
  by_contra hcontra
  simp only [prop3d4₀func, hcontra] at hi
  exact hi rfl


/-
Key property of the recursion: when the process has not terminated at step `i+1`, the `μA`-value
strictly increases from step `i` to step `i+1`.

This is extracted directly from the choice of a minimal “improving” element in `ℒₛ`.
-/
lemma prop3d4₀func_defprop1
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i + 1)).val) :
μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩
  > μA μ ⟨(I.val.1 , (prop3d4₀func μ I i).val) , lt_of_le_of_ne ((prop3d4₀func μ I i)).prop.1 <|
  prop3d4₀func_helper μ I i hi⟩ := by
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra] at hi
    simp only [↓reduceDIte, ne_eq, not_true_eq_false] at hi
  simpa only [hne] using (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <|
    prop3d4₀func_helper μ I i hi) hne).choose_spec.1.out.choose_spec.choose_spec


/-
Another key property of the recursion: step `i+1` is chosen to be “maximal among those with at least
its `μA`-value”, in the sense that no `z` strictly between step `i+1` and step `i` can have
`μA (I.left, z)` greater-or-equal to `μA (I.left, step(i+1))`.

This is a tie-breaking/optimality condition derived from minimality in the well-founded `has_min`
choice.
-/
lemma prop3d4₀func_defprop2
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(i : ℕ) (hi : I.val.1 ≠ (prop3d4₀func μ I (i + 1)).val) :
∀ z : ℒ, (hz : (prop3d4₀func μ I (i+1)).val < z ∧ z ≤ (prop3d4₀func μ I i).val) →
    ¬ μA μ ⟨(I.val.1, z),lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1⟩ ≥
      μA μ ⟨(I.val.1 , (prop3d4₀func μ I (i+1)).val) ,
        lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ := by
  intro z hz
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi]
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra] at hi
    simp only [↓reduceDIte, ne_eq, not_true_eq_false] at hi
  simp only [hne]
  by_contra hcontra
  have h' : z ∈ (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) := by
    use ⟨le_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i + 1)).prop.1 hz.1,
      le_trans hz.2 (prop3d4₀func μ I i).prop.2⟩
    have h'' : z < (prop3d4₀func μ I i).val := by
      apply lt_of_le_of_ne hz.2
      by_contra hcontra'
      simp only [hcontra', ↓reduceDIte, ge_iff_le] at hcontra
      exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne
        ).choose_spec.1.out.choose_spec.choose_spec.not_ge hcontra
    use ⟨ne_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1,h''⟩, lt_of_le_of_lt'
      hcontra.ge (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi)
      hne).choose_spec.1.out.choose_spec.choose_spec
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hne] at hz
  exact (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne
    ).choose_spec.2 z h' hz.1


/-
The recursion produces a strictly decreasing chain of underlying values until it reaches the left
endpoint.

More precisely: if step `i` is not the left endpoint, then `(prop3d4₀func μ I i).val > (prop3d4₀func
μ I (i+1)).val`.
-/
lemma prop3d4₀func_strict_decreasing
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) :
∀ i : ℕ, I.val.1 ≠ (prop3d4₀func μ I i).val →
(prop3d4₀func μ I i).val > (prop3d4₀func μ I (i+1)).val := by
  intro i hi
  by_cases h: I.val.1 = (prop3d4₀func μ I (i+1)).val
  · simp only [prop3d4₀func, hi, ↓reduceDIte] at h
    by_cases hne : (ℒₛ μ I (prop3d4₀func μ I i) hi).Nonempty
    · simp only [hne, ↓reduceDIte] at h
      exact False.elim ((inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) hi) hne
        ).choose_spec.1.out.choose_spec.choose.1 h)
    · simp only [prop3d4₀func, hi, hne]
      exact lt_of_le_of_ne (prop3d4₀func μ I i).prop.1 hi
  · simp only [prop3d4₀func, hi]
    have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i h).Nonempty := by
      by_contra hcontra
      simp only [prop3d4₀func, prop3d4₀func_helper μ I i h, hcontra,
        ↓reduceDIte, not_true_eq_false] at h
    simpa only [hne] using (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I i) hi) hne
      ).choose_spec.1.out.choose_spec.choose.2


/-
Finite-length termination: under the DCC hypothesis on `μA`, the recursion reaches the left endpoint
in finitely many steps.

API note: the proof uses the fact that the recursion yields a strict anti-chain of underlying
elements
and simultaneously a strict increase in `μA`, contradicting DCC if it never hits the left endpoint.
-/
lemma prop3d4₀func_fin_len
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μA_DescendingChainCondition μ) :
∃ i : ℕ, (prop3d4₀func μ I i).val = I.val.1 := by
  by_contra!
  let func := fun m : ℕ => (prop3d4₀func μ I m).val
  have h₀ : ∀ i : ℕ, func i > I.val.1 := by
    intro i
    rw [gt_iff_lt]
    exact Ne.lt_of_le (this i).symm  (prop3d4₀func μ I i).prop.1
  have h₂ := fun t ↦ prop3d4₀func_defprop1 μ I t (this (t + 1)).symm
  have ttt := fun t ↦ prop3d4₀func_strict_decreasing μ I t (this t).symm
  rcases (hμDCC.μ_dcc I.val.1 func h₀ (strictAnti_nat_of_succ_lt ttt)) with ⟨N, hN⟩
  exact hN (h₂ N)


/-
Define the length `prop3d4₀func_len μ I hμDCC` as the first time the recursion hits the left
endpoint.

This is the `Nat.find` of the termination statement `prop3d4₀func_fin_len`.
-/
noncomputable def prop3d4₀func_len
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μA_DescendingChainCondition μ) : ℕ := by
  letI := Classical.propDecidable
  exact Nat.find (prop3d4₀func_fin_len μ I hμDCC)


/-
The termination length is nonzero.

Intuitively, at step `0` the recursion starts at the right endpoint, which cannot equal the left
endpoint for a strict interval.
-/
lemma prop3d4₀func_len_nonzero
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ) :
prop3d4₀func_len μ I hμDCC ≠ 0 := by
  letI := Classical.propDecidable
  by_contra hcontra
  have h : (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC)).val = I.val.1 :=
    Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
  simp only [hcontra, prop3d4₀func] at h
  exact (lt_self_iff_false I.val.1).1 (h ▸ I.prop)


/-
Before termination, every step lies strictly above the left endpoint.

This lemma is phrased as a strict inequality `I.left < (prop3d4₀func μ I i).val` for `i < len`.
-/
lemma prop3d4₀func_defprop3₀
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ)
(i : ℕ) (hi : i < (prop3d4₀func_len μ I hμDCC)) :
I.val.1 < (prop3d4₀func μ I i).val := by
  letI := Classical.propDecidable
  exact ((Nat.find_min (prop3d4₀func_fin_len μ I hμDCC)) hi).decidable_imp_symm
    fun hcontra ↦ (eq_of_le_of_not_lt (prop3d4₀func μ I i).prop.1 hcontra).symm


/-
Optimality at the last pre-termination step.

Let `len` be the first index such that step `len` equals `I.left`. Then at index `len-1`, no
intermediate point `y` between `I.left` and `(func (len-1)).val` yields a strictly larger value of
`μA (I.left, y)`.

This is used to show that the final candidate satisfies the selection predicate `S₁I`.
-/
lemma prop3d4₀func_defprop3
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμDCC : μA_DescendingChainCondition μ)
(y : ℒ) (hy : I.val.1 < y ∧ y ≤ (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) :
¬ μA μ ⟨(I.val.1,y),hy.1⟩ >
  μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) ,
    prop3d4₀func_defprop3₀ μ I hμDCC ((prop3d4₀func_len μ I hμDCC) - 1) <| Nat.sub_one_lt <|
    prop3d4₀func_len_nonzero μ I hμDCC⟩ := by
  letI := Classical.propDecidable
  let len := prop3d4₀func_len μ I hμDCC
  by_contra hcontra
  by_cases hcases : y < (prop3d4₀func μ I (len - 1)).val
  · have h₂ : (prop3d4₀func μ I len).val = I.val.1 := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
    have h₃ : ¬ (ℒₛ μ I (prop3d4₀func μ I <| len - 1) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC
      (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))).Nonempty := by
      by_contra hcontra'
      have triv : len - 1 + 1 = len :=  Nat.sub_one_add_one <| prop3d4₀func_len_nonzero μ I hμDCC
      rw [← (triv)] at h₂
      simp only [prop3d4₀func, ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1)
        (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC)] at h₂
      simp only [↓reduceDIte, hcontra'] at h₂
      apply (inst_3.wf.has_min (ℒₛ μ I (prop3d4₀func μ I (len-1)) (ne_of_lt <|
        prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <|
        prop3d4₀func_len_nonzero μ I hμDCC))) hcontra').choose_spec.1.out.choose_spec.choose.1
        h₂.symm
    refine h₃ ?_
    use y, ⟨le_of_lt hy.1,le_trans hy.2 (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC - 1)
      ).prop.2⟩, ⟨ne_of_lt hy.1,hcases⟩
  · simp only [eq_of_le_of_not_lt hy.2 hcases] at hcontra
    exact (lt_self_iff_false <| μA μ ⟨(I.val.1 , (prop3d4₀func μ I <| len - 1).val) ,
      prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) <| Nat.sub_one_lt <|
      prop3d4₀func_len_nonzero μ I hμDCC⟩).1 hcontra


/-
Proposition 3.4: nonemptiness of the set of stable breakpoints `StI μ I`.

Under well-foundedness and the DCC hypothesis, and assuming convexity on `I`, the selection
predicates `S₁I`/`S₂I` can be satisfied by a canonical choice produced by the recursion
`prop3d4₀func`.

API note: this provides the key existential input for later uniqueness/maximality arguments.
-/
lemma prop3d4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμDCC : μA_DescendingChainCondition μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
: (StI μ I).Nonempty := by
  letI := Classical.propDecidable
  let len := prop3d4₀func_len μ I hμDCC
  let func:= prop3d4₀func μ I
  by_cases h : len = 1
  · refine ⟨I.val.2, ⟨le_of_lt I.prop, le_rfl⟩, ne_of_lt I.prop,⟨?_,fun _ hyI _ _ ↦ hyI.2⟩⟩
    intro y hyI hy
    have h' :=
      (congrArg (fun _a ↦ (func (_a - 1)).val = I.val.2) h) ▸ (of_eq_true (eq_self I.val.2))
    have h'' : ¬ μA μ ⟨(I.val.1, y), lt_of_le_of_ne hyI.1 hy⟩ > μA μ ⟨(I.val.1, (func (len-1)).val),
      prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) <| Nat.sub_one_lt <|
      prop3d4₀func_len_nonzero μ I hμDCC⟩
        := prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.left hy,h' ▸ hyI.2⟩
    simp only [h', Prod.mk.eta, Subtype.coe_eta, gt_iff_lt] at h''
    exact h''
  · have h₂ : ∀ i : ℕ, i ≤ len -1 → I.val.1 ≠ (func i).val := by
      intro i hi
      by_contra!
      exact (Nat.find_min (prop3d4₀func_fin_len μ I hμDCC) <| Nat.lt_of_le_sub_one
        (Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC) hi) this.symm
    have h₃ : ∀ i : ℕ, (hi : 1 ≤ i ∧ i ≤ len -1) → (∀ y : ℒ, (hyI : InIntvl I y) →
      (hy : I.val.1 ≠ y) → (y < func (i-1) ∧ μA μ ⟨(I.val.1, y), lt_of_le_of_ne hyI.1 hy⟩ ≥
      μA μ ⟨(I.val.1, (func i).val), lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩) →
      y ≤ (func i).val) := by
      intro i hi y hyI hy hy'
      by_contra!
      have h₃' : (func i).val < y ⊔ (func i).val ∧ y ⊔ (func i).val ≤ (func (i-1)).val := by
        refine ⟨right_lt_sup.2 this, sup_le_iff.2 ⟨le_of_lt hy'.1,?_⟩⟩
        have h₃'' : (prop3d4₀func μ I (i - 1)).val > (prop3d4₀func μ I (i - 1 + 1)).val :=
          prop3d4₀func_strict_decreasing μ I (i-1) (h₂ (i-1) <| le_trans (le_of_lt <|
            Nat.sub_one_lt <| Nat.one_le_iff_ne_zero.1 hi.1) hi.2)
        rw [Nat.sub_one_add_one] at h₃''
        · apply le_of_lt h₃''
        · exact Nat.one_le_iff_ne_zero.1 hi.1
      have h₃''' : ∀ (hi' : I.val.1 ≠ (func i).val) (z : ℒ) (hz : (func i).val < z ∧
        z ≤ (func (i - 1)).val), ¬ μA μ ⟨(I.val.1, z), lt_of_le_of_lt (func i).prop.1 hz.1⟩ ≥
        μA μ ⟨(I.val.1, (func (i - 1 + 1)).val), lt_of_le_of_ne ((func (i - 1 + 1)).prop).1
        ((Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2)⟩ :=
        fun hi' z hz ↦ prop3d4₀func_defprop2 μ I (i - 1) ( (Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2) z ((Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ hz)
      simp only [ne_eq, not_false_eq_true, Nat.sub_add_cancel, ge_iff_le, forall_const, hi,
        h₂] at h₃'''
      exact (h₃''' (y ⊔ func i) h₃') <| inf_eq_right.2 hy'.2 ▸ impl.prop2d8₁I I μ hμcvx y hyI
        (func i) (func i).prop I.val.1 ⟨le_rfl,le_of_lt I.prop⟩  ⟨lt_of_le_of_ne hyI.1 hy,
        lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩
    have h₄ : ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → μA μ ⟨(I.val.1, y) ,
      lt_of_le_of_ne hyI.1 hy⟩ ≥ μA μ ⟨(I.val.1, (func (len - 1)).val) , lt_of_le_of_ne (func
      (len - 1)).prop.1 <| h₂ (len - 1) le_rfl⟩ → (∀ i : ℕ, i ≤ len - 1 → y ≤ (func i).val) := by
      intro y hyI hy hy' i hi
      induction i with
      | zero =>
        simp only [func,prop3d4₀func]
        exact hyI.2
      | succ i hi' =>
        have hfinal : ∀ j : ℕ, (hj : j ≤ len - 1) → μA μ ⟨(I.val.1, (func (len - 1)).val),
          lt_of_le_of_ne ((func (len - 1)).prop).1 (h₂ (len - 1) le_rfl)⟩ ≥ μA μ ⟨(I.val.1, func j),
          prop3d4₀func_defprop3₀ μ I hμDCC j <| lt_of_le_of_lt hj <| Nat.sub_one_lt <| ne_of_gt <|
          Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC⟩
         := by
          apply Nat.decreasingInduction
          · exact fun k hk hk' ↦  le_of_lt <| lt_of_lt_of_le (prop3d4₀func_defprop1 μ I k <|
              ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (k+1) <| Nat.add_lt_of_lt_sub hk) hk'
          · exact le_rfl
        have hh : y < func i := by
          refine lt_of_le_of_ne (hi' (Nat.le_of_succ_le hi)) ?_
          by_contra!
          have hhh :=  lt_of_le_of_lt' hy' <| lt_of_le_of_lt' (hfinal (i+1) hi) <|
            prop3d4₀func_defprop1 μ I i (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (i+1) <|
            lt_of_le_of_lt hi <| Nat.sub_one_lt <| ne_of_gt <| Nat.zero_lt_of_ne_zero <|
            prop3d4₀func_len_nonzero μ I hμDCC)
          simp only [this] at hhh
          exact irrefl _ hhh
        exact h₃ (i+1) ⟨Nat.le_add_left 1 i,hi⟩ y hyI hy ⟨hh,ge_trans hy' (hfinal (i+1) hi)⟩
    use (func (len - 1)).val
    constructor
    · refine ⟨h₂ (len - 1) le_rfl,⟨?_,fun y hyI hy hy' ↦
        (fun y hyI hy h ↦ h₄ y hyI hy h (len - 1) le_rfl) y hyI hy <| ge_of_eq hy'⟩⟩
      intro y hyI hy
      by_contra!
      exact prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.1 hy,
        (fun y hyI hy h ↦ h₄ y hyI hy h (len - 1) le_rfl) y hyI hy <| le_of_lt this⟩ this
    · exact (func (len - 1)).prop


/-
Remark 3.5: uniqueness of stable breakpoints in a complete linear order.

If the target lattice `S` is a complete linear order, then any two elements of `StI μ I` must be
equal.

This uses the tie-breaking predicate `S₂I` together with totality of comparisons in `S`.
-/
lemma rmk3d5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hySt : y ∈ StI μ I) : x = y := by
  rcases hxSt with ⟨hxI,⟨hx,⟨hxS₁,hxS₂⟩⟩⟩
  rcases hySt with ⟨hyI,⟨hy,⟨hyS₁,hyS₂⟩⟩⟩
  exact eq_of_le_of_ge (hyS₂ x hxI hx (eq_of_le_of_ge (le_of_not_gt <| hxS₁ y hyI hy)
    (le_of_not_gt <| hyS₁ x hxI hx)).symm) (hxS₂ y hyI hy <| eq_of_le_of_ge
    (le_of_not_gt <| hxS₁ y hyI hy) (le_of_not_gt <| hyS₁ x hxI hx))


/-
Proposition 3.7 (part 1): a stable breakpoint induces semistability of the corresponding
subinterval.

If `x ∈ StI μ I`, then the interval `(I.left, x)` is semistable in the interval-local sense
`semistableI`.
-/
lemma prop3d7₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxSt : x ∈ StI μ I) :
semistableI μ ⟨(I.val.1 , x), lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ := by
  rcases hxSt with ⟨hxI,⟨hx',⟨hx'',hxS₂I⟩⟩⟩
  exact ⟨⟨hxI.1,le_rfl⟩, hx', ⟨fun z hzI hz ↦ hx'' z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz,
    fun z hzI hz hz' ↦ hxS₂I z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz hz'⟩⟩


/-
Proposition 3.7 (part 2): strict inequality obstruction above a stable breakpoint.

Assuming convexity, if `x ∈ StI μ I` and `y > x` lies in `I`, then `μA (I.left, x)` is not
less-or-equal to `μA (x,y)`.

Intuition: above the chosen breakpoint, the interval `(x,y)` cannot dominate the “best” value at
`x`.
-/
lemma prop3d7₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(x : ℒ) (hxSt : x ∈ StI μ I) :
∀ y : ℒ, (hyI : InIntvl I y) → (hy : y > x) → ¬ μA μ ⟨(I.val.1 , x) ,
  lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨(x, y), hy⟩ := by
  by_contra!
  rcases this with ⟨y,⟨hyI,⟨hy,hy'⟩⟩⟩
  exact (not_le_of_gt hy) (hxSt.out.choose_spec.choose_spec.2 y hyI
    (ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hy) <|eq_of_le_of_not_lt' ((inf_eq_left.2 hy') ▸
    impl.prop2d6₁I I μ hμcvx I.val.1 ⟨le_rfl,le_of_lt I.prop⟩ x hxSt.out.choose y hyI
    ⟨lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose,hy⟩) <|
    hxSt.out.choose_spec.choose_spec.1 y hyI <| ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hy)


/-
Proposition 3.8 (part 1): totality on `StI μ I` under comparability/attainment hypotheses.

Under convexity and well-foundedness, if either:
- the target `S` is totally ordered, or
- all relevant `μA` infima are attained,
then the order on the set of stable breakpoints becomes total.

API note: this produces an instance of `Std.Total` for the subtype `StI μ I`.
-/
lemma prop3d8₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)-- (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) →
       IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
@Std.Total (StI μ I) (· ≤ ·) := by
  refine { total := ?_ }
  rintro ⟨x,hx⟩ ⟨x',hx'⟩
  have h₁ : IsComparable (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hx.out.choose.1
    hx.out.choose_spec.choose⟩) (μA μ ⟨(I.val.1,x'),lt_of_le_of_ne hx'.out.choose.1
    hx'.out.choose_spec.choose⟩) ∨ IsAttained μ ⟨(I.val.1 , x ⊔ x') , lt_sup_of_lt_right <|
    lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩:= by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hx.out.choose.1
        hx.out.choose_spec.choose⟩) (μA μ ⟨(I.val.1,x'),lt_of_le_of_ne hx'.out.choose.1
        hx'.out.choose_spec.choose⟩)
    · exact Or.inr <| hattained  (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2
        hx'.out.choose.2⟩ <| ne_of_lt <| lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1
        hx.out.choose_spec.choose
  have h₂ : μA μ ⟨(I.val.1, x), lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩ =
    μA μ ⟨(I.val.1, x ⊔ x'), lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1
    hx.out.choose_spec.choose⟩ ∨ μA μ ⟨(I.val.1, x'), lt_of_le_of_ne hx'.out.choose.1
    hx'.out.choose_spec.choose⟩ = μA μ ⟨(I.val.1, x ⊔ x'), lt_sup_of_lt_left <|
    lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose⟩ := by
    rcases (impl.prop2d8₂I I μ hμcvx x hx.out.choose x' hx'.out.choose I.val.1
      ⟨le_rfl,le_of_lt I.prop⟩ ⟨lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose,
      lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose⟩ h₁) with c1 | c2
    · exact Or.inl <| eq_of_le_of_not_lt c1 <| hx.out.choose_spec.choose_spec.1 (x ⊔ x')
        ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩ <| ne_of_lt <|
        lt_sup_of_lt_left <| lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose
    · exact Or.inr <| eq_of_le_of_not_lt c2 <| hx'.out.choose_spec.choose_spec.1 (x ⊔ x')
        ⟨le_sup_of_le_left hx.out.choose.1,sup_le hx.out.choose.2 hx'.out.choose.2⟩ <| ne_of_lt <|
        lt_sup_of_lt_right <| lt_of_le_of_ne hx'.out.choose.1 hx'.out.choose_spec.choose
  have h₃ : x ⊔ x' ≤ x ∨ x ⊔ x' ≤ x' := by
    rcases h₂ with c1 | c2
    · exact Or.inl <| hx.out.choose_spec.choose_spec.2 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,
        sup_le hx.out.choose.2 hx'.out.choose.2⟩  (ne_of_lt <| lt_sup_of_lt_left <|
        lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose) c1.symm
    · exact Or.inr <| hx'.out.choose_spec.choose_spec.2 (x ⊔ x') ⟨le_sup_of_le_left hx.out.choose.1,
      sup_le hx.out.choose.2 hx'.out.choose.2⟩  (ne_of_lt <| lt_sup_of_lt_left <|
      lt_of_le_of_ne hx.out.choose.1 hx.out.choose_spec.choose) c2.symm
  rcases h₃ with c1 | c2
  · exact Or.inr (sup_le_iff.1 c1).2
  · exact Or.inl (sup_le_iff.1 c2).1


/-
Existence of a greatest element of `StI μ I`.

Assuming the DCC (as a typeclass), convexity, and one of the comparability/attainment hypotheses,
we obtain an element `s` that is greatest in the set `StI μ I`.

API note: the proof uses `has_min` on `StI μ I` together with the totality lemma `prop3d8₁`.
-/
lemma prop3d8₁' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) →
       IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)  :
∃ s : ℒ, IsGreatest (StI μ I) s := by
  rcases inst_3.wf.has_min (StI μ I) (prop3d4 μ hμ I hμcvx) with ⟨M,hM⟩
  refine ⟨M,⟨hM.1,mem_upperBounds.2 ?_⟩⟩
  intro x hx
  rcases (prop3d8₁ μ I hμcvx h).total ⟨x, hx⟩ ⟨M, hM.1⟩ with c1 | c2
  · exact c1
  · exact le_of_eq <| eq_of_le_of_not_lt' c2 (hM.2 x hx)


/-
Proposition 3.8 (part 2): decomposition at a stable breakpoint.

Under convexity and the comparability/attainment hypothesis, if `x ∈ StI μ I` and `x<y` in `I`, then
`μA (I.left, y) = μA (x,y)`.

Intuition: once `x` is chosen as a stable breakpoint, the “best value” up to `y` is fully determined
by the subinterval starting at `x`.
-/
lemma prop3d8₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)-- (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2}) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) →
       IsAttained μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hyI : InIntvl I y)
(hxy : x < y) :
μA μ ⟨(I.val.1 , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩ := by
  have h : IsComparable (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hxSt.out.choose.1
    hxSt.out.choose_spec.choose⟩) (μA μ ⟨(x,y), hxy⟩) ∨ IsAttained μ ⟨(I.val.1,y),
    lt_of_le_of_lt hxSt.out.choose.1 hxy⟩:= by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total (μA μ ⟨(I.val.1,x),lt_of_le_of_ne hxSt.out.choose.1
        hxSt.out.choose_spec.choose⟩) (μA μ ⟨(x,y), hxy⟩)
    · exact Or.inr <| hattained y hyI (ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hxy)
  rcases (impl.prop2d6₃I I μ hμcvx I.val.1 ⟨le_rfl,le_of_lt I.prop⟩ x hxSt.out.choose y hyI
    ⟨lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose,hxy⟩ h) with c1 | c2
  · exact c1.symm
  · exact False.elim  ((not_lt_of_ge <| hxSt.out.choose_spec.choose_spec.2 y hyI  (ne_of_lt <|
      lt_of_le_of_lt hxSt.out.choose.1 hxy) <| eq_of_le_of_not_lt' c2.1
      (hxSt.out.choose_spec.choose_spec.1 y hyI <| ne_of_lt <| lt_of_le_of_lt hxSt.out.choose.1 hxy)
      ) hxy)


/-
Equivalence between the global typeclass `Semistable μ` and interval-local semistability on the
total interval.

This lemma is an API bridge: it lets one freely move between the class-based semistability used in
later modules and the predicate `semistableI μ TotIntvl` defined via `StI`.
-/
theorem semistable_iff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
  Semistable μ ↔ semistableI μ TotIntvl := by
  simp only [semistableI, StI, S₁I, TotIntvl, ne_eq, gt_iff_lt, S₂I, Set.mem_setOf_eq, le_top,
    implies_true, and_true, bot_ne_top, not_false_eq_true, exists_true_left]
  constructor
  · intro h
    use in_TotIntvl _
    exact fun y hyI hy ↦ h.semistable y <| Ne.symm hy
  · exact fun h ↦ {semistable := fun y hyI hy ↦ (h.choose_spec y (in_TotIntvl _) (Ne.symm hyI)) hy}


/-
Small rewriting helper: chain three equalities.

This is used to keep some long proofs readable when transporting equalities across definitional
expansions.
-/
lemma smart_helper {α : Type*} {a b c d : α} (h : a = b) (h' : b = c) (h'' : c = d) : a = d :=
h ▸ h' ▸ h''

/-
Transport semistability along restriction.

This theorem relates:
- `semistableI μ I`, i.e. semistability of the interval `I` with respect to `μ`, and
- `Semistable (Resμ I μ)`, i.e. global semistability of the restricted function on the interval
  subtype.

API note: this is a key adapter used whenever proofs switch between the “ambient interval” viewpoint
and the “interval as a bounded lattice” viewpoint.
-/
theorem semistableI_iff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : semistableI μ I ↔ Semistable (Resμ I μ) := by
  rw [semistable_iff]
  unfold Resμ
  constructor
  · intro h
    simp only [semistableI]
    simp only [semistableI] at h
    rcases h.out with ⟨h1,h2,h3,h4⟩
    use in_TotIntvl (TotIntvl.val).2
    use ne_of_lt (TotIntvl.prop)
    constructor
    · simp only [S₁I, ne_eq, Prod.mk.eta, Subtype.coe_eta, gt_iff_lt] at *
      intro y hyI hy
      have := h3 y hyI (Subtype.coe_ne_coe.2 hy)
      by_contra fine
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq fine ?_)
      · simp only [μA, ne_eq]
        congr 1
        ext
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,ha1.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          simp only [Set.mem_setOf_eq]
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            exact ⟨b.val, ⟨⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩,rfl⟩⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩
            constructor
            · rfl
            · exact ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · rintro ⟨b,⟨hb1,hb2⟩⟩
          rw [← hb2]
          use b
          refine ⟨⟨hb1.1,?_⟩,?_⟩
          · by_contra h'
            exact hb1.2 <| Subtype.coe_eq_of_eq_mk h'
          · simp only [μmax, ne_eq]
            congr 1; ext
            constructor
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use ⟨c,⟨le_trans b.prop.1 hc1.1.1,hc1.1.2⟩⟩, ⟨hc1.1,Subtype.coe_ne_coe.1 hc1.2⟩
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use c.val, ⟨hc1.1,Subtype.coe_ne_coe.2 hc1.2⟩
      · simp only [μA, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩,
              ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            simp only [Set.mem_setOf_eq]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 y.prop.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩,
              ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
    · simp only [S₂I, ne_eq, Prod.mk.eta, Subtype.coe_eta, le_top, implies_true] at *
  · rintro ⟨h1,⟨h3,⟨h4,h5⟩⟩⟩
    simp only [semistableI, StI, ne_eq, Set.mem_setOf_eq]
    use ⟨le_of_lt I.prop,le_rfl⟩, ne_of_lt I.prop
    constructor
    · simp only [S₁I, ne_eq, gt_iff_lt, Prod.mk.eta, Subtype.coe_eta] at *
      intro y hyI hy
      have := h4 ⟨y,hyI⟩ (in_TotIntvl _) (Subtype.coe_ne_coe.1 hy)
      by_contra h
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq h ?_)
      · simp only [μA, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans a.prop.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · intro h
            rcases h with ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,ha1.1.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,hb1.1.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
      · simp only [μA, ne_eq]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 hyI.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩,
              ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
        · intro h
          rcases h with ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp only [μmax, ne_eq]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 hyI.2⟩⟩,
              ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
    · simp only [S₂I, ne_eq, le_top, implies_true, Prod.mk.eta, Subtype.coe_eta] at *
      intro y hyI hy h
      exact hyI.2


end impl

end HarderNarasimhan
