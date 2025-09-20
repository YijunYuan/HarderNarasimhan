import Mathlib.Tactic
import Mathlib.Data.Finset.Sort

namespace Lex'Order

scoped instance (priority := 114514) LexLE {α : Type*} [LinearOrder α] : LE (Finset α) where
  le A B := (A.card < B.card) ∨ (A.card = B.card) ∧ (A.sort (LE.le) ≤ B.sort (LE.le))

scoped instance (priority := 114514) LexLT {α : Type*} [LinearOrder α] : LT (Finset α) where
  lt A B := A ≤ B ∧ A ≠ B

scoped instance (priority := 114513) {α : Type*} [LinearOrder α] (A B : Finset α) : Decidable (A ≤ B) := id (id instDecidableOr)

private lemma helper {P Q : Prop} : P ∨ Q ↔ P ∨ ((¬ P) ∧ Q) := by
  tauto

private lemma inj_sort {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r] : Function.Injective (Finset.sort r) := by
  intro _ _ h
  refine Finset.ext fun x ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · exact (Finset.mem_sort r).1 <| h ▸ (Finset.mem_sort r).2 h'
  · exact (Finset.mem_sort r).1 <| h ▸ (Finset.mem_sort r).2 h'

private lemma le_antisymm {α : Type*} [LinearOrder α] : ∀ (a b : Finset α), a ≤ b → b ≤ a → a = b := by
  intro A B h1 h2
  unfold LE.le LexLE at h1 h2
  simp only at *
  cases' h1 with h1 h1
  · cases' h2 with h2 h2
    · linarith
    · linarith
  · cases' h2 with h2 h2
    · linarith
    · exact inj_sort _ <| eq_of_le_of_le h1.2 h2.2

private lemma le_card {α : Type*} [LinearOrder α] (A B : Finset α) : A ≤ B → A.card ≤ B.card := by
  intro h
  have h' := h
  by_contra!
  cases' h with h h
  · linarith
  · exact (lt_self_iff_false B.card).mp <| (le_antisymm A B h' <| id (id (id (Or.inl this)))) ▸ this

private def Lex'LinearOrder {α : Type*} [LinearOrder α] : LinearOrder (Finset α) where
  le := LexLE.le
  le_antisymm := le_antisymm
  le_refl := by
    intro A
    unfold LE.le LexLE
    simp only [lt_self_iff_false, le_refl, or_true]
    tauto
  le_trans := by
    intro A B C hAB hBC
    have t1 := le_card A B hAB
    have t2 := le_card B C hBC
    unfold LE.le LexLE at hAB hBC
    simp only at *
    cases' (helper.1 hAB) with h1 h1
    · cases' (helper.1 hBC) with h2 h2
      · exact Or.inl <| lt_trans h1 h2
      · unfold LE.le LexLE
        exact Or.inl <| Nat.lt_of_lt_of_le h1 t2
    · cases' (helper.1 hBC) with h2 h2
      · unfold LE.le LexLE
        exact Or.inl <| Nat.lt_of_le_of_lt t1 h2
      · unfold LE.le LexLE
        simp only
        right
        constructor
        · linarith
        · exact le_trans h1.2.2 h2.2.2
  lt_iff_le_not_ge := by
    intro A B
    constructor
    · intro h
      unfold LT.lt LexLT at h
      simp only [ne_eq] at h
      exact ⟨h.1,fun this ↦ h.2 <| le_antisymm A B h.1 this⟩
    · intro h
      unfold LT.lt LexLT
      simp only [ne_eq]
      exact ⟨h.1,fun this ↦ (and_not_self_iff (B ≤ B)).mp <| this ▸ h⟩
  toDecidableLE := by
    unfold DecidableLE LE.le LexLE DecidableRel
    intro A B
    simp only [not_lt]
    exact inferInstance
  min := fun A B ↦ if A ≤ B then A else B
  min_def := by
    intro A B
    simp only [ite_eq_ite]
  max := fun A B ↦ if A ≤ B then B else A
  max_def := by
    intro A B
    simp only [ite_eq_ite]
  le_total := by
    intro A B
    refine Decidable.or_iff_not_imp_left.mpr ?_
    intro h
    unfold LE.le LexLE at h
    simp only at h
    have h : ¬(A.card < B.card) ∧ (¬ (A.card = B.card) ∨ ¬ (Finset.sort LE.le A ≤ Finset.sort LE.le B)) := by tauto
    have h1 := h.1
    have h2 := h.2
    unfold LE.le LexLE
    simp only
    cases' helper.1 h2 with h2 h2
    · left
      apply le_of_not_gt at h1
      apply lt_of_le_of_ne h1 <| Ne.symm h2
    · right
      simp only [Decidable.not_not, not_le] at h2
      refine ⟨?_,le_of_lt h2.2⟩
      simp only [not_lt] at h1
      exact h2.1.symm

theorem Lex'Order_prop (α : Type*) [lo : LinearOrder α] : ∃ lo : LinearOrder (Finset α),
(∀ A B : Finset α, A ⊆ B → lo.le A B) ∧
(∀ a b : α, a ≤ b ↔ lo.le {a} {b}) := by
  use Lex'LinearOrder
  constructor
  · intro A B h
    unfold LE.le Preorder.toLE PartialOrder.toPreorder LinearOrder.toPartialOrder Lex'LinearOrder LexLE
    if heq : A = B then
      right
      constructor
      · exact congrArg Finset.card heq
      · rw [heq]
    else
      left
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.2 ⟨h,heq⟩
  · intro a b
    unfold LE.le Preorder.toLE PartialOrder.toPreorder LinearOrder.toPartialOrder Lex'LinearOrder LexLE
    simp only [SemilatticeInf.toPartialOrder, Lattice.toSemilatticeInf,
      SemilatticeSup.toPartialOrder, Lattice.toSemilatticeSup, DistribLattice.toLattice,
      instDistribLatticeOfLinearOrder, LinearOrder.toLattice, LinearOrder.toPartialOrder,
      Finset.card_singleton, lt_self_iff_false, Finset.sort_singleton, true_and, false_or]
    constructor
    · intro h
      unfold LE.le List.LE' Preorder.toLE PartialOrder.toPreorder LinearOrder.toPartialOrder List.instLinearOrder
      simp only [List.lex_lt, List.cons.injEq, and_true]
      if h' : a = b then
        exact Or.inl h'
      else
        right
        unfold LT.lt List.instLT
        simp only [List.lex_singleton_iff]
        exact lt_of_le_of_ne h h'
    · intro h
      unfold LE.le List.LE' Preorder.toLE PartialOrder.toPreorder LinearOrder.toPartialOrder List.instLinearOrder at h
      simp only [List.lex_lt, List.cons.injEq, and_true] at h
      cases' h with h h
      · exact le_of_eq h
      · unfold LT.lt List.instLT at h
        simp only [List.lex_singleton_iff] at h
        exact le_of_lt h

end Lex'Order
