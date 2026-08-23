/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
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

/--
Proposition 3.2 (interval-local form): monotonicity of `μA` under enlarging the right endpoint,
in the special case where `μA (x,z) = ⊤`.

Assuming convexity on `I`, if `x<z` and `μA (x,z)` is top, then for any `a<x` in the interval,
we have `μA (a,x) ≤ μA (a,z)`.

API note: this lemma is used to derive a descending chain condition by contradiction.
-/
lemma prop3d2 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(I : Intvl ℒ)
(μ : Intvl ℒ → S) (hμcvx : ConvexI I μ)
(x : ℒ) (hxI : x ∈ I)
(z : ℒ) (hzI : z ∈ I)
(h : x < z)
(h' : μA μ ⟨x, z, h⟩ = ⊤)
(a : ℒ) (haI : a ∈ I) (hax : a < x) :
μA μ ⟨a, x , hax⟩ ≤ μA μ ⟨a, z , lt_trans hax h⟩ := by
  have h'' := impl.prop2d6₁I I μ hμcvx a haI x hxI z hzI ⟨hax,h⟩
  rwa [h', inf_top_eq] at h''


/--
Corollary 3.3: a convenient sufficient condition for the DCC on `μA`.

Given a hypothesis that any strict descending chain `f` eventually produces an interval
`(f(N+1), f(N))` with `μA = ⊤`, we deduce the class `μA_DescendingChainCondition μ`.

API note: this turns a “top occurs along chains” assumption into the formal DCC typeclass.
-/
lemma cor3d3 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : Intvl ℒ → S) (hμcvx : ConvexI ⊤ μ)
(h : ∀ f : ℕ → ℒ, (h : StrictAnti f) →  ∃N : ℕ, μA μ ⟨f <| N + 1, f N,h (lt_add_one N)⟩ = ⊤)
: μA_DescendingChainCondition μ := by
  refine { μ_dcc := fun a f h₁ h₂ ↦ ?_ }
  obtain ⟨N, hN⟩ := h f h₂
  exact ⟨N, not_lt_of_ge <| prop3d2 ⊤ μ hμcvx (f <| N + 1)
    (Intvl.mem_top <| f <| N + 1) (f N) (Intvl.mem_top <| f N)
    (h₂ (lt_add_one N)) hN a (Intvl.mem_top <| a) (h₁ <| N + 1)⟩


/--
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
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(x : ↥I) (hx : I.left ≠ x) : Set ℒ :=
{p : ℒ | ∃ h₁ : p ∈ I, ∃ h₂ : I.left ≠ p ∧ p < x,
  μA μ ⟨I.left, p,lt_of_le_of_ne h₁.1 h₂.1⟩ >
  μA μ ⟨I.left, x.val , lt_of_le_of_ne x.prop.1 hx⟩}


open Classical in
/--
Core recursive construction used in Proposition 3.4.

`prop3d4₀func μ I k` produces a point of the interval `I` (as a subtype `{p // p}` ∈ I) by
iterating:
- start at the right endpoint for `k=0`,
- if the previous point is the left endpoint, stay there,
- otherwise, if there is a “strictly improving” point in `ℒₛ`, pick a minimal such point using
  well-foundedness,
- if there is no improvement, jump to the left endpoint.

API note: the definition is noncomputable due to classical choice and well-founded `min`.
-/
noncomputable def prop3d4₀func
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [h : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(k : ℕ) : ↥I :=
  match k with
  | 0 => ⟨I.right, I.right_mem⟩
  | n+1 =>
    let prev := prop3d4₀func μ I n
    if hbot : I.left = prev.val then
      ⟨I.left, I.left_mem⟩
    else
      if hne : (ℒₛ μ I prev hbot).Nonempty then
        ⟨h.wf.min (ℒₛ μ I prev hbot) hne, (h.wf.min_mem (ℒₛ μ I prev hbot) hne).out.choose⟩
      else
        ⟨I.left, I.left_mem⟩


/--
Helper lemma: if step `i+1` is not at the left endpoint, then step `i` is also not at the left
endpoint.

This is used repeatedly to justify that the “improvement set” `ℒₛ` is well-defined at earlier steps.
-/
lemma prop3d4₀func_helper {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(i : ℕ) (hi : I.left ≠ (prop3d4₀func μ I (i + 1)).val) :
I.left ≠ (prop3d4₀func μ I i).val := by
  by_contra hcontra
  simp only [prop3d4₀func, hcontra, ↓reduceDIte, ne_eq, not_true_eq_false] at hi


/--
Key property of the recursion: when the process has not terminated at step `i+1`, the `μA`-value
strictly increases from step `i` to step `i+1`.

This is extracted directly from the choice of a minimal “improving” element in `ℒₛ`.
-/
lemma prop3d4₀func_defprop1
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(i : ℕ) (hi : I.left ≠ (prop3d4₀func μ I (i + 1)).val) :
μA μ ⟨I.left, (prop3d4₀func μ I (i+1)).val , lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩
  > μA μ ⟨I.left, (prop3d4₀func μ I i).val , lt_of_le_of_ne ((prop3d4₀func μ I i)).prop.1 <|
  prop3d4₀func_helper μ I i hi⟩ := by
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra, ↓reduceDIte, ne_eq,
      not_true_eq_false] at hi
  simpa only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hne, ↓reduceDIte] using
    (inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I i) <|
      prop3d4₀func_helper μ I i hi) hne).out.choose_spec.choose_spec


/--
Another key property of the recursion: step `i+1` is chosen to be “maximal among those with at least
its `μA`-value”, in the sense that no `z` strictly between step `i+1` and step `i` can have
`μA (I.left, z)` greater-or-equal to `μA (I.left, step(i+1))`.

This is a tie-breaking/optimality condition derived from minimality in the well-founded `min`
choice.
-/
lemma prop3d4₀func_defprop2
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(i : ℕ) (hi : I.left ≠ (prop3d4₀func μ I (i + 1)).val) :
∀ z : ℒ, (hz : (prop3d4₀func μ I (i+1)).val < z ∧ z ≤ (prop3d4₀func μ I i).val) →
    ¬ μA μ ⟨I.left, z,lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1⟩ ≥
      μA μ ⟨I.left, (prop3d4₀func μ I (i+1)).val ,
        lt_of_le_of_ne (prop3d4₀func μ I (i+1)).prop.1 hi⟩ := by
  intro z hz
  have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi).Nonempty := by
    by_contra hcontra
    simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hcontra, ↓reduceDIte, ne_eq,
      not_true_eq_false] at hi
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hne]
  by_contra hcontra
  have h' : z ∈ (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) := by
    use ⟨le_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i + 1)).prop.1 hz.1,
      le_trans hz.2 (prop3d4₀func μ I i).prop.2⟩
    have h'' : z < (prop3d4₀func μ I i).val := by
      apply lt_of_le_of_ne hz.2
      intro hcontra'
      simp only [hcontra', ↓reduceDIte, ge_iff_le] at hcontra
      exact (inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi) hne
        ).out.choose_spec.choose_spec.not_ge hcontra
    use ⟨ne_of_lt <| lt_of_le_of_lt (prop3d4₀func μ I (i+1)).prop.1 hz.1,h''⟩, lt_of_le_of_lt'
      hcontra.ge (inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi)
      hne).out.choose_spec.choose_spec
  simp only [prop3d4₀func, prop3d4₀func_helper μ I i hi, hne] at hz
  exact inst_3.wf.not_lt_min (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i hi)
    h' hz.1


/--
The recursion produces a strictly decreasing chain of underlying values until it reaches the left
endpoint.

More precisely: if step `i` is not the left endpoint, then `(prop3d4₀func μ I i).val > (prop3d4₀func
μ I (i+1)).val`.
-/
lemma prop3d4₀func_strict_decreasing
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ) :
∀ i : ℕ, I.left ≠ (prop3d4₀func μ I i).val →
(prop3d4₀func μ I i).val > (prop3d4₀func μ I (i+1)).val := by
  intro i hi
  by_cases h: I.left = (prop3d4₀func μ I (i+1)).val
  · simp only [prop3d4₀func, hi, ↓reduceDIte] at h
    by_cases hne : (ℒₛ μ I (prop3d4₀func μ I i) hi).Nonempty
    · simp only [hne, ↓reduceDIte] at h
      exact False.elim ((inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I i) hi) hne
        ).out.choose_spec.choose.1 h)
    · simp only [prop3d4₀func, hi, hne]
      exact lt_of_le_of_ne (prop3d4₀func μ I i).prop.1 hi
  · simp only [prop3d4₀func, hi, ↓reduceDIte]
    have hne : (ℒₛ μ I (prop3d4₀func μ I i) <| prop3d4₀func_helper μ I i h).Nonempty := by
      by_contra hcontra
      simp only [prop3d4₀func, prop3d4₀func_helper μ I i h, hcontra,
        ↓reduceDIte, not_true_eq_false] at h
    simpa only [hne, ↓reduceDIte] using (inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I i) hi) hne
      ).out.choose_spec.choose.2


/--
Finite-length termination: under the DCC hypothesis on `μA`, the recursion reaches the left endpoint
in finitely many steps.

API note: the proof uses the fact that the recursion yields a strict anti-chain of underlying
elements
and simultaneously a strict increase in `μA`, contradicting DCC if it never hits the left endpoint.
-/
lemma prop3d4₀func_fin_len
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(hμDCC : μA_DescendingChainCondition μ) :
∃ i : ℕ, (prop3d4₀func μ I i).val = I.left := by
  by_contra!
  obtain ⟨N, hN⟩ := hμDCC.μ_dcc I.left (fun m ↦ (prop3d4₀func μ I m).val)
    (fun i ↦ Ne.lt_of_le (this i).symm (prop3d4₀func μ I i).prop.1)
    (strictAnti_nat_of_succ_lt fun t ↦ prop3d4₀func_strict_decreasing μ I t (this t).symm)
  exact hN (prop3d4₀func_defprop1 μ I N (this (N + 1)).symm)


open Classical in
/--
Define the length `prop3d4₀func_len μ I hμDCC` as the first time the recursion hits the left
endpoint.

This is the `Nat.find` of the termination statement `prop3d4₀func_fin_len`.
-/
noncomputable def prop3d4₀func_len
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(hμDCC : μA_DescendingChainCondition μ) : ℕ :=
  Nat.find (prop3d4₀func_fin_len μ I hμDCC)


/--
The termination length is nonzero.

Intuitively, at step `0` the recursion starts at the right endpoint, which cannot equal the left
endpoint for a strict interval.
-/
lemma prop3d4₀func_len_nonzero
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ) (hμDCC : μA_DescendingChainCondition μ) :
prop3d4₀func_len μ I hμDCC ≠ 0 := by
  classical
  by_contra hcontra
  have h : (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC)).val = I.left :=
    Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
  simp only [hcontra, prop3d4₀func] at h
  exact (h ▸ I.lt).false


/--
Before termination, every step lies strictly above the left endpoint.

This lemma is phrased as a strict inequality `I.left < (prop3d4₀func μ I i).val` for `i < len`.
-/
lemma prop3d4₀func_defprop3₀
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ) (hμDCC : μA_DescendingChainCondition μ)
(i : ℕ) (hi : i < (prop3d4₀func_len μ I hμDCC)) :
I.left < (prop3d4₀func μ I i).val := by
  classical
  exact ((Nat.find_min (prop3d4₀func_fin_len μ I hμDCC)) hi).decidable_imp_symm
    fun hcontra ↦ (eq_of_le_of_not_lt (prop3d4₀func μ I i).prop.1 hcontra).symm


/--
Optimality at the last pre-termination step.

Let `len` be the first index such that step `len` equals `I.left`. Then at index `len-1`, no
intermediate point `y` between `I.left` and `(func (len-1)).val` yields a strictly larger value of
`μA (I.left, y)`.

This is used to show that the final candidate satisfies the selection predicate `S₁I`.
-/
lemma prop3d4₀func_defprop3
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ) (hμDCC : μA_DescendingChainCondition μ)
(y : ℒ) (hy : I.left < y ∧ y ≤ (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val) :
¬ μA μ ⟨I.left, y,hy.1⟩ >
  μA μ ⟨I.left, (prop3d4₀func μ I <| (prop3d4₀func_len μ I hμDCC) - 1).val ,
    prop3d4₀func_defprop3₀ μ I hμDCC ((prop3d4₀func_len μ I hμDCC) - 1) <| Nat.sub_one_lt <|
    prop3d4₀func_len_nonzero μ I hμDCC⟩ := by
  classical
  let len := prop3d4₀func_len μ I hμDCC
  by_contra hcontra
  by_cases hcases : y < (prop3d4₀func μ I (len - 1)).val
  · have h₂ : (prop3d4₀func μ I len).val = I.left := Nat.find_spec (prop3d4₀func_fin_len μ I hμDCC)
    have h₃ : ¬ (ℒₛ μ I (prop3d4₀func μ I <| len - 1) (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC
      (len - 1) (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC))).Nonempty := by
      by_contra hcontra'
      have triv : len - 1 + 1 = len := Nat.sub_one_add_one <| prop3d4₀func_len_nonzero μ I hμDCC
      rw [← triv] at h₂
      simp only [prop3d4₀func, ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (len - 1)
        (Nat.sub_one_lt <| prop3d4₀func_len_nonzero μ I hμDCC), hcontra', ↓reduceDIte] at h₂
      exact (inst_3.wf.min_mem (ℒₛ μ I (prop3d4₀func μ I (len-1)) (ne_of_lt <|
        prop3d4₀func_defprop3₀ μ I hμDCC (len - 1) (Nat.sub_one_lt <|
        prop3d4₀func_len_nonzero μ I hμDCC))) hcontra').out.choose_spec.choose.1
        h₂.symm
    exact h₃ ⟨y, ⟨le_of_lt hy.1, le_trans hy.2 (prop3d4₀func μ I (len - 1)).prop.2⟩,
      ⟨ne_of_lt hy.1, hcases⟩, hcontra⟩
  · simp only [eq_of_le_of_not_lt hy.2 hcases] at hcontra
    exact lt_irrefl _ hcontra


/--
Proposition 3.4: nonemptiness of the set of stable breakpoints `StI μ I`.

Under well-foundedness and the DCC hypothesis, and assuming convexity on `I`, the selection
predicates `S₁I`/`S₂I` can be satisfied by a canonical choice produced by the recursion
`prop3d4₀func`.

API note: this provides the key existential input for later uniqueness/maximality arguments.
-/
lemma prop3d4 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (hμDCC : μA_DescendingChainCondition μ)
(I : Intvl ℒ) (hμcvx : ConvexI I μ)
: (StI μ I).Nonempty := by
  classical
  let len := prop3d4₀func_len μ I hμDCC
  let func:= prop3d4₀func μ I
  by_cases h : len = 1
  · refine ⟨I.right, I.right_mem, I.lt.ne,⟨?_,fun _ hyI _ _ ↦ hyI.2⟩⟩
    intro y hyI hy
    have h' : (prop3d4₀func μ I (prop3d4₀func_len μ I hμDCC - 1)).val = I.right :=
      congrArg (fun a ↦ (func (a - 1)).val) h
    simpa only [h', Prod.mk.eta, Subtype.coe_eta, gt_iff_lt] using
      prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.left hy, h' ▸ hyI.2⟩
  · have h₂ : ∀ i : ℕ, i ≤ len -1 → I.left ≠ (func i).val := by
      intro i hi
      by_contra!
      exact (Nat.find_min (prop3d4₀func_fin_len μ I hμDCC) <| Nat.lt_of_le_sub_one
        (Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC) hi) this.symm
    have h₃ : ∀ i : ℕ, (hi : 1 ≤ i ∧ i ≤ len -1) → (∀ y : ℒ, (hyI : y ∈ I) →
      (hy : I.left ≠ y) → (y < func (i-1) ∧ μA μ ⟨I.left, y, lt_of_le_of_ne hyI.1 hy⟩ ≥
      μA μ ⟨I.left, (func i).val, lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩) →
      y ≤ (func i).val) := by
      intro i hi y hyI hy hy'
      by_contra!
      have h₃' : (func i).val < y ⊔ (func i).val ∧ y ⊔ (func i).val ≤ (func (i-1)).val := by
        refine ⟨right_lt_sup.2 this, sup_le_iff.2 ⟨le_of_lt hy'.1,?_⟩⟩
        have h₃'' := prop3d4₀func_strict_decreasing μ I (i-1) (h₂ (i-1) <| le_trans (le_of_lt <|
          Nat.sub_one_lt <| Nat.one_le_iff_ne_zero.1 hi.1) hi.2)
        rw [Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1] at h₃''
        exact le_of_lt h₃''
      have h₃''' : ∀ (hi' : I.left ≠ (func i).val) (z : ℒ) (hz : (func i).val < z ∧
        z ≤ (func (i - 1)).val), ¬ μA μ ⟨I.left, z, lt_of_le_of_lt (func i).prop.1 hz.1⟩ ≥
        μA μ ⟨I.left, (func (i - 1 + 1)).val, lt_of_le_of_ne ((func (i - 1 + 1)).prop).1
        ((Nat.sub_one_add_one <| Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2)⟩ :=
        fun hi' z hz ↦ prop3d4₀func_defprop2 μ I (i - 1) ( (Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ h₂ i hi.2) z ((Nat.sub_one_add_one <|
          Nat.one_le_iff_ne_zero.1 hi.1) ▸ hz)
      simp only [ne_eq, not_false_eq_true, Nat.sub_add_cancel, ge_iff_le, forall_const, hi,
        h₂] at h₃'''
      exact (h₃''' (y ⊔ func i) h₃') <| inf_eq_right.2 hy'.2 ▸ impl.prop2d8₁I I μ hμcvx y hyI
        (func i) (func i).prop I.left I.left_mem  ⟨lt_of_le_of_ne hyI.1 hy,
        lt_of_le_of_ne (func i).prop.1 <| h₂ i hi.2⟩
    have h₄ : ∀ y : ℒ, (hyI : y ∈ I) → (hy : I.left ≠ y) → μA μ ⟨I.left, y ,
      lt_of_le_of_ne hyI.1 hy⟩ ≥ μA μ ⟨I.left, (func (len - 1)).val , lt_of_le_of_ne (func
      (len - 1)).prop.1 <| h₂ (len - 1) le_rfl⟩ → (∀ i : ℕ, i ≤ len - 1 → y ≤ (func i).val) := by
      intro y hyI hy hy' i hi
      induction i with
      | zero => exact hyI.2
      | succ i hi' =>
        have hfinal : ∀ j : ℕ, (hj : j ≤ len - 1) → μA μ ⟨I.left, (func (len - 1)).val,
          lt_of_le_of_ne ((func (len - 1)).prop).1 (h₂ (len - 1) le_rfl)⟩ ≥ μA μ ⟨I.left, func j,
          prop3d4₀func_defprop3₀ μ I hμDCC j <| lt_of_le_of_lt hj <| Nat.sub_one_lt <| ne_of_gt <|
          Nat.zero_lt_of_ne_zero <| prop3d4₀func_len_nonzero μ I hμDCC⟩ := by
          apply Nat.decreasingInduction
          · exact fun k hk hk' ↦  le_of_lt <| lt_of_lt_of_le (prop3d4₀func_defprop1 μ I k <|
              ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (k+1) <| Nat.add_lt_of_lt_sub hk) hk'
          · exact le_rfl
        have hh : y < func i := by
          refine lt_of_le_of_ne (hi' (Nat.le_of_succ_le hi)) ?_
          intro heq
          have hhh := lt_of_le_of_lt' hy' <| lt_of_le_of_lt' (hfinal (i+1) hi) <|
            prop3d4₀func_defprop1 μ I i (ne_of_lt <| prop3d4₀func_defprop3₀ μ I hμDCC (i+1) <|
            lt_of_le_of_lt hi <| Nat.sub_one_lt <| ne_of_gt <| Nat.zero_lt_of_ne_zero <|
            prop3d4₀func_len_nonzero μ I hμDCC)
          simp only [heq] at hhh
          exact irrefl _ hhh
        exact h₃ (i+1) ⟨Nat.le_add_left 1 i,hi⟩ y hyI hy ⟨hh,ge_trans hy' (hfinal (i+1) hi)⟩
    refine ⟨(func (len - 1)).val, (func (len - 1)).prop, h₂ (len - 1) le_rfl, ?_,
      fun y hyI hy hy' ↦ h₄ y hyI hy (ge_of_eq hy') (len - 1) le_rfl⟩
    intro y hyI hy
    by_contra!
    exact prop3d4₀func_defprop3 μ I hμDCC y ⟨lt_of_le_of_ne hyI.1 hy,
      h₄ y hyI hy (le_of_lt this) (len - 1) le_rfl⟩ this


/--
Remark 3.5: uniqueness of stable breakpoints in a complete linear order.

If the target lattice `S` is a complete linear order, then any two elements of `StI μ I` must be
equal.

This uses the tie-breaking predicate `S₂I` together with totality of comparisons in `S`.
-/
lemma rmk3d5 {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hySt : y ∈ StI μ I) : x = y := by
  rcases hxSt with ⟨hxI, hx, hxS₁, hxS₂⟩
  rcases hySt with ⟨hyI, hy, hyS₁, hyS₂⟩
  have e := eq_of_le_of_ge (le_of_not_gt <| hxS₁ y hyI hy) (le_of_not_gt <| hyS₁ x hxI hx)
  exact eq_of_le_of_ge (hyS₂ x hxI hx e.symm) (hxS₂ y hyI hy e)


/--
Proposition 3.7 (part 1): a stable breakpoint induces semistability of the corresponding
subinterval.

If `x ∈ StI μ I`, then the interval `(I.left, x)` is semistable in the interval-local sense
`semistableI`.
-/
lemma prop3d7₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ)
(x : ℒ) (hxSt : x ∈ StI μ I) :
semistableI μ ⟨I.left, x, lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ := by
  rcases hxSt with ⟨hxI,⟨hx',⟨hx'',hxS₂I⟩⟩⟩
  exact ⟨⟨hxI.1,le_rfl⟩, hx', ⟨fun z hzI hz ↦ hx'' z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz,
    fun z hzI hz hz' ↦ hxS₂I z ⟨hzI.1,le_trans hzI.2 hxI.2⟩ hz hz'⟩⟩


/--
Proposition 3.7 (part 2): strict inequality obstruction above a stable breakpoint.

Assuming convexity, if `x ∈ StI μ I` and `y > x` lies in `I`, then `μA (I.left, x)` is not
less-or-equal to `μA (x,y)`.

Intuition: above the chosen breakpoint, the interval `(x,y)` cannot dominate the “best” value at
`x`.
-/
lemma prop3d7₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)
(I : Intvl ℒ) (hμcvx : ConvexI I μ)
(x : ℒ) (hxSt : x ∈ StI μ I) :
∀ y : ℒ, (hyI : y ∈ I) → (hy : y > x) → ¬ μA μ ⟨I.left, x ,
  lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨x, y, hy⟩ := by
  obtain ⟨hxI, hxne, hxS₁, hxS₂⟩ := hxSt.out
  intro y hyI hy hy'
  exact (not_le_of_gt hy) (hxS₂ y hyI (ne_of_lt <| lt_of_le_of_lt hxI.1 hy) <|
    eq_of_le_of_not_lt' ((inf_eq_left.2 hy') ▸ impl.prop2d6₁I I μ hμcvx I.left
    I.left_mem x hxI y hyI ⟨lt_of_le_of_ne hxI.1 hxne,hy⟩) <|
    hxS₁ y hyI <| ne_of_lt <| lt_of_le_of_lt hxI.1 hy)


/--
Proposition 3.8 (part 1): totality on `StI μ I` under comparability/attainment hypotheses.

Under convexity and well-foundedness, if either:
- the target `S` is totally ordered, or
- all relevant `μA` infima are attained,
then the order on the set of stable breakpoints becomes total.

API note: this produces an instance of `Std.Total` for the subtype `StI μ I`.
-/
lemma prop3d8₁ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)-- (hμ : μDCC μ)
(I : Intvl ℒ) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
       IsAttained μ ⟨I.left, z , lt_of_le_of_ne hzI.left hz⟩) :
@Std.Total (StI μ I) (· ≤ ·) := by
  refine { total := ?_ }
  rintro ⟨x,hx⟩ ⟨x',hx'⟩
  obtain ⟨hxI, hxne, hxS₁, hxS₂⟩ := hx.out
  obtain ⟨hx'I, hx'ne, hx'S₁, hx'S₂⟩ := hx'.out
  have hxlt : I.left < x := lt_of_le_of_ne hxI.1 hxne
  have hx'lt : I.left < x' := lt_of_le_of_ne hx'I.1 hx'ne
  have hsI : (x ⊔ x') ∈ I := ⟨le_sup_of_le_left hxI.1, sup_le hxI.2 hx'I.2⟩
  have hsne : I.left ≠ x ⊔ x' := ne_of_lt <| lt_sup_of_lt_left hxlt
  have h₁ : IsComparable (μA μ ⟨I.left, x, hxlt⟩) (μA μ ⟨I.left, x', hx'lt⟩) ∨
      IsAttained μ ⟨I.left, x ⊔ x' , lt_sup_of_lt_right hx'lt⟩ := by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total _ _
    · exact Or.inr <| hattained (x ⊔ x') hsI hsne
  have h₂ : μA μ ⟨I.left, x, hxlt⟩ = μA μ ⟨I.left, x ⊔ x', lt_sup_of_lt_left hxlt⟩ ∨
      μA μ ⟨I.left, x', hx'lt⟩ = μA μ ⟨I.left, x ⊔ x', lt_sup_of_lt_left hxlt⟩ := by
    rcases impl.prop2d8₂I I μ hμcvx x hxI x' hx'I I.left
      I.left_mem ⟨hxlt, hx'lt⟩ h₁ with c1 | c2
    · exact Or.inl <| eq_of_le_of_not_lt c1 <| hxS₁ (x ⊔ x') hsI hsne
    · exact Or.inr <| eq_of_le_of_not_lt c2 <| hx'S₁ (x ⊔ x') hsI hsne
  rcases h₂ with c1 | c2
  · exact Or.inr (sup_le_iff.1 <| hxS₂ (x ⊔ x') hsI hsne c1.symm).2
  · exact Or.inl (sup_le_iff.1 <| hx'S₂ (x ⊔ x') hsI hsne c2.symm).1


/--
Existence of a greatest element of `StI μ I`.

Assuming the DCC (as a typeclass), convexity, and one of the comparability/attainment hypotheses,
we obtain an element `s` that is greatest in the set `StI μ I`.

API note: the proof uses `has_min` on `StI μ I` together with the totality lemma `prop3d8₁`.
-/
lemma prop3d8₁' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) (hμ : μA_DescendingChainCondition μ)
(I : Intvl ℒ) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
       IsAttained μ ⟨I.left, z , lt_of_le_of_ne hzI.left hz⟩)  :
∃ s : ℒ, IsGreatest (StI μ I) s := by
  obtain ⟨M, hM⟩ := inst_3.wf.has_min (StI μ I) (prop3d4 μ hμ I hμcvx)
  refine ⟨M, hM.1, mem_upperBounds.2 fun x hx ↦ ?_⟩
  exact ((prop3d8₁ μ I hμcvx h).total ⟨x, hx⟩ ⟨M, hM.1⟩).elim id
    fun c2 ↦ le_of_eq <| eq_of_le_of_not_lt' c2 (hM.2 x hx)


/--
Proposition 3.8 (part 2): decomposition at a stable breakpoint.

Under convexity and the comparability/attainment hypothesis, if `x ∈ StI μ I` and `x<y` in `I`, then
`μA (I.left, y) = μA (x,y)`.

Intuition: once `x` is chosen as a stable breakpoint, the “best value” up to `y` is fully determined
by the subinterval starting at `x`.
-/
lemma prop3d8₂ {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S)-- (hμ : μDCC μ)
(I : Intvl ℒ) (hμcvx : ConvexI I μ)
(h : (@Std.Total S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : z ∈ I) → (hz : I.left ≠ z) →
       IsAttained μ ⟨I.left, z , lt_of_le_of_ne hzI.left hz⟩)
(x : ℒ) (hxSt : x ∈ StI μ I)
(y : ℒ) (hyI : y ∈ I)
(hxy : x < y) :
μA μ ⟨I.left, y, lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨x, y, hxy⟩ := by
  obtain ⟨hxI, hxne, hxS₁, hxS₂⟩ := hxSt.out
  have hxlt : I.left < x := lt_of_le_of_ne hxI.1 hxne
  have hyne : I.left ≠ y := ne_of_lt <| lt_of_le_of_lt hxI.1 hxy
  have h : IsComparable (μA μ ⟨I.left, x, hxlt⟩) (μA μ ⟨x, y, hxy⟩) ∨
      IsAttained μ ⟨I.left, y, lt_of_le_of_lt hxI.1 hxy⟩ := by
    rcases h with htotal | hattained
    · exact Or.inl <| htotal.total _ _
    · exact Or.inr <| hattained y hyI hyne
  rcases impl.prop2d6₃I I μ hμcvx I.left I.left_mem x hxI y hyI
    ⟨hxlt, hxy⟩ h with c1 | c2
  · exact c1.symm
  · exact absurd hxy <| not_lt_of_ge <| hxS₂ y hyI hyne <|
      eq_of_le_of_not_lt' c2.1 (hxS₁ y hyI hyne)


/--
Equivalence between the global typeclass `Semistable μ` and interval-local semistability on the
total interval.

This lemma is an API bridge: it lets one freely move between the class-based semistability used in
later modules and the predicate `semistableI μ ⊤` defined via `StI`.
-/
theorem semistable_iff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : Intvl ℒ → S) :
  Semistable μ ↔ semistableI μ ⊤ := by
  simp only [semistableI, StI, S₁I, Intvl.left_top, Intvl.right_top, ne_eq, gt_iff_lt, S₂I,
    Set.mem_ofPred_eq, le_top,
    implies_true, and_true, bot_ne_top, not_false_eq_true, exists_true_left]
  constructor
  · exact fun h ↦ ⟨Intvl.mem_top _, fun y hyI hy ↦ h.semistable y <| bot_le.lt_of_ne hy⟩
  · exact fun h ↦ {semistable := fun y hyI hy ↦ (h.choose_spec y (Intvl.mem_top _) hyI.ne) hy}


/--
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
(μ : Intvl ℒ → S)
(I : Intvl ℒ) : semistableI μ I ↔ Semistable (Resμ I μ) := by
  rw [semistable_iff (μ := Resμ I μ)]
  simp only [semistableI, StI, S₁I, S₂I, Intvl.left_top, Intvl.right_top, Set.mem_ofPred_eq,
    gt_iff_lt,
    μA_res_intvl]
  constructor
  · rintro ⟨hI, hne, h₁, h₂⟩
    exact ⟨Intvl.mem_top _, ne_of_lt bot_lt_top,
      fun y hyI hy ↦ h₁ y y.prop (fun h => hy <| Subtype.ext h),
      fun y hyI hy hy' ↦ h₂ y y.prop (fun h => hy <| Subtype.ext h) hy'⟩
  · rintro ⟨hI, hne, h₁, h₂⟩
    exact ⟨I.right_mem, I.lt.ne,
      fun y hyI hy ↦ h₁ ⟨y, hyI⟩ (Intvl.mem_top _) (fun h => hy <| congrArg Subtype.val h),
      fun y hyI hy hy' ↦ hyI.2⟩


end impl

end HarderNarasimhan
