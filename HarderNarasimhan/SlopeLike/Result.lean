import HarderNarasimhan.SlopeLike.Impl

/-!
This file exposes the main user-facing results of the `SlopeLike` module.

The `SlopeLike` axiom in
[HarderNarasimhan/SlopeLike/Defs.lean](HarderNarasimhan/SlopeLike/Defs.lean) is given
as four conjunctive inequalities that work in a general complete lattice. The implementation file
`SlopeLike/Impl.lean` proves an equivalent “seesaw” formulation as a disjunction of three patterns.

This file:
- re-exports that equivalence as `seesaw`,
- provides a convenient theorem `SlopeLike_of_μQuotient` constructing slope-like functions from the
  quotient construction `μQuotient`,
- derives a more implication-oriented helper lemma `seesaw'` for common proof patterns.
-/

namespace HarderNarasimhan

/-
Public seesaw characterization of `SlopeLike μ`.

This is a direct re-export of `impl.prop4d6`. It states that for every triple `x<y<z`, the three
values `μ(x,y)`, `μ(x,z)`, `μ(y,z)` are either strictly increasing, strictly decreasing, or all
equal.

API note: this form is often significantly easier to use in proofs than the original four-conjunct
definition.
-/
lemma seesaw {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
SlopeLike μ ↔
∀ (x y z : ℒ), (h : x < y ∧ y < z) → (
  μ ⟨(x, y), h.1⟩ < μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ < μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ > μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ > μ ⟨(y, z), h.2⟩
  ∨
  μ ⟨(x, y), h.1⟩ = μ ⟨(x, z), lt_trans h.1 h.2⟩ ∧ μ ⟨(x, z), lt_trans h.1 h.2⟩ = μ ⟨(y, z), h.2⟩
)
------------
:= impl.prop4d6 μ


/-
Construct a slope-like function from the quotient construction `μQuotient`.

This theorem packages `impl.prop4d8` as a user-facing API:
given additivity of rank `r` and degree `d` on composable intervals and a positivity condition when
`r=0`, the induced `μQuotient r d` is slope-like.
-/
theorem SlopeLike_of_μQuotient {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{V : Type*} [TotallyOrderedRealVectorSpace V] [Nontrivial V]
(r : {p :ℒ × ℒ // p.1 < p.2} → NNReal)
(d : {p :ℒ × ℒ // p.1 < p.2} → V)
(h₁ : ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
  d ⟨(x, z), lt_trans h.1 h.2⟩ = d ⟨(x, y), h.1⟩ + d ⟨(y, z), h.2⟩ ∧
  r ⟨(x, z), lt_trans h.1 h.2⟩ = r ⟨(x, y), h.1⟩ + r ⟨(y, z), h.2⟩)
(h₂ : ∀ (x y : ℒ), (h : x < y) → r ⟨(x, y), h⟩ = 0 → d ⟨(x, y), h⟩ > 0) :
------------
 SlopeLike (μQuotient r d)
------------
:= impl.prop4d8 r d h₁ h₂


/-
An implication-style reformulation of the seesaw behavior.

Assuming `SlopeLike μ`, this lemma provides several “if one comparison holds, then the other two
follow” statements, separately for the increasing, decreasing, and constant cases.

API note: this is tailored for forward reasoning in proofs where one inequality is known and the
remaining relations need to be derived.
-/
lemma seesaw' {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
SlopeLike μ → ∀ (x y z : ℒ), (h : x < y ∧ y < z) →
(
  (
    μ ⟨(x,y),h.1⟩ < μ ⟨(x,z),lt_trans h.1 h.2⟩ →
      μ ⟨(x,y),h.1⟩ < μ ⟨(y,z),h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ < μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,y),h.1⟩ < μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ < μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ < μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,z),lt_trans h.1 h.2⟩ < μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ < μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,y),h.1⟩ < μ ⟨(y,z),h.2⟩
  )
) ∧ (
  (
    μ ⟨(x,y),h.1⟩ > μ ⟨(x,z),lt_trans h.1 h.2⟩ →
      μ ⟨(x,y),h.1⟩ > μ ⟨(y,z),h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ > μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,y),h.1⟩ > μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ > μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ > μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,z),lt_trans h.1 h.2⟩ > μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ > μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,y),h.1⟩ > μ ⟨(y,z),h.2⟩
  )
) ∧ (
  (
    μ ⟨(x,y),h.1⟩ = μ ⟨(x,z),lt_trans h.1 h.2⟩ →
      μ ⟨(x,y),h.1⟩ = μ ⟨(y,z),h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ = μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,y),h.1⟩ = μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ = μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,z),lt_trans h.1 h.2⟩ = μ ⟨(y,z),h.2⟩
  ) ∧ (
    μ ⟨(x,z),lt_trans h.1 h.2⟩ = μ ⟨(y,z),h.2⟩ →
      μ ⟨(x,y),h.1⟩ = μ ⟨(x,z),lt_trans h.1 h.2⟩ ∧ μ ⟨(x,y),h.1⟩ = μ ⟨(y,z),h.2⟩
  )
) := by
  intro hsl x y z h
  have h1 := (seesaw μ).1 hsl x y z h
  refine ⟨?_,⟨?_,⟨fun _ ↦ by aesop,⟨fun h' ↦ (Or.resolve_left <| Or.resolve_left h1 <|
    fun t ↦ (lt_self_iff_false _).1 <| h' ▸ lt_trans t.1 t.2) fun t ↦ (lt_self_iff_false _).1 <|
    h' ▸ gt_trans t.1 t.2,fun _ ↦ by aesop⟩⟩⟩⟩
  · rw [← or_assoc] at h1
    refine ⟨fun h' ↦ ?_,⟨fun h' ↦ (Or.resolve_right <| Or.resolve_right h1 <|
      fun t ↦ (lt_self_iff_false _).1 <| t.1 ▸ t.2 ▸ h')
      fun t ↦ (not_lt_of_gt <| gt_trans t.1 t.2) h',fun h' ↦ ?_⟩⟩
    · have := (Or.resolve_right <| Or.resolve_right h1 <|
        fun t ↦ (lt_self_iff_false _).1 <| t.1 ▸ h') fun t ↦ (not_lt_of_gt t.1) h'
      exact ⟨lt_trans this.1 this.2, this.2⟩
    · have := (Or.resolve_right <| Or.resolve_right h1 <|
        fun t ↦ (lt_self_iff_false _).1 <| t.2 ▸ h') fun t ↦ (not_lt_of_gt h') t.2
      exact ⟨this.1,lt_trans this.1 this.2⟩
  · refine ⟨fun h' ↦ ?_,⟨fun h' ↦  (Or.resolve_right <| Or.resolve_left h1 <|
      fun t ↦ not_lt_of_gt h' (lt_trans t.1 t.2))
      fun t ↦ (lt_self_iff_false _).1 <| t.1 ▸ t.2 ▸ h',fun h' ↦ ?_⟩⟩
    · have := (Or.resolve_right <| Or.resolve_left h1 (fun t ↦ not_lt_of_gt h' t.left))
        (fun t ↦ (lt_self_iff_false (μ ⟨(x, z), lt_trans h.1 h.2⟩)).1 (t.1 ▸ h'))
      exact ⟨gt_trans this.1 this.2,this.2⟩
    · have := (Or.resolve_right <| Or.resolve_left h1 <| fun t ↦ (not_lt_of_gt t.2) h')
        fun t ↦ (lt_self_iff_false _).1 <| t.2 ▸ h'
      exact ⟨this.1,gt_trans this.1 this.2⟩

end HarderNarasimhan
