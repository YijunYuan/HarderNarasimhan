import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Closure

namespace OrderTheory
instance {α : Type*} [PartialOrder α] (T : ClosureOperator (Set α)): CompleteLattice (ClosureOperator.Closeds T) where
  top :=⟨Set.univ,ClosureOperator.isClosed_iff_closure_le.mpr fun ⦃a⦄ a ↦ trivial⟩
  le_top A := fun ⦃a⦄ a ↦ trivial
  bot := ⟨T ∅, ClosureOperator.isClosed_closure T ∅⟩
  bot_le A := by
    intro a ha
    simp only at *
    exact (ClosureOperator.IsClosed.closure_eq A.property) ▸ (T.monotone <| Set.empty_subset A.val) ha
  inf A B := ⟨A.val ∩ B.val,ClosureOperator.isClosed_iff_closure_le.mpr fun x hx ↦ (ClosureOperator.IsClosed.closure_eq A.property) ▸ (ClosureOperator.IsClosed.closure_eq B.property) ▸ ⟨(T.monotone <| Set.inter_subset_left) hx,(T.monotone <| Set.inter_subset_right) hx⟩⟩
  le_inf A B C h1 h2 := fun a ha ↦ ⟨h1 ha,h2 ha⟩
  inf_le_left A B := fun ⦃a⦄ b ↦ b.1
  inf_le_right A B := fun ⦃a⦄ b ↦ b.right
  sup A B := ⟨T (A.val ∪ B.val), ClosureOperator.isClosed_closure T (A.val ∪ B.val)⟩
  sup_le A B C h1 h2 := by
    intro a ha
    simp only at *
    exact (ClosureOperator.IsClosed.closure_eq C.property) ▸ (T.monotone <| Set.union_subset h1 h2) ha
  le_sup_left := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq A.property).symm]
    exact ClosureOperator.monotone T Set.subset_union_left
  le_sup_right := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq B.property).symm]
    exact ClosureOperator.monotone T Set.subset_union_right
  sInf 𝒮 := by
    refine ⟨⋂ a ∈ 𝒮, a.val,ClosureOperator.isClosed_iff_closure_le.mpr fun x hx ↦ ?_⟩
    simp only [Set.mem_iInter, Subtype.forall] at *
    refine fun S hS hSb ↦ (ClosureOperator.IsClosed.closure_eq hS) ▸ T.monotone (fun x hx ↦ ?_) hx
    simp only [Set.mem_iInter, Subtype.forall] at hx
    exact hx S hS hSb
  le_sInf 𝒮 A hA := by
    intro x h
    simp only [Subtype.forall, Set.mem_iInter] at *
    exact fun S hS hSb ↦ hA S hS hSb h
  sInf_le 𝒮 A:= by
    intro hA x hx
    simp only [Set.mem_iInter, Subtype.forall] at *
    exact hx A.val A.prop hA
  sSup 𝒮 := ⟨T (⋃ a ∈ 𝒮, a.val),ClosureOperator.isClosed_closure T (⋃ a ∈ 𝒮, a.val)⟩
  le_sSup 𝒮 A hA:= fun x hx ↦ ClosureOperator.monotone T (Set.subset_biUnion_of_mem hA) <| (ClosureOperator.IsClosed.closure_eq A.property).symm ▸ hx
  sSup_le 𝒮 A hA := by
    intro x hx
    simp only
    refine (ClosureOperator.IsClosed.closure_eq A.property) ▸ ClosureOperator.monotone T (fun y hy ↦ ?_) hx
    simp only [Set.mem_iUnion, exists_prop, Subtype.exists, exists_and_right] at hy
    exact Exists.casesOn hy fun S h ↦ And.casesOn h fun left hSb ↦ Exists.casesOn left fun hS hP ↦ hA ⟨S, hS⟩ hP hSb


section DedekindMacNeille
lemma DedekindMacNeilleConnection (α : Type*) [PartialOrder α] : GaloisConnection (fun A ↦ (OrderDual.toDual (upperBounds A))) (fun A : (Set α)ᵒᵈ ↦ lowerBounds A.ofDual) := fun _ _ ↦ ⟨fun h _ ha ⦃_⦄ a_3 ↦ h a_3 ha, fun h _ ha ⦃_⦄ a_2 ↦ h a_2 ha⟩


def DedekindMacNeilleClosureOperator (α : Type*) [PartialOrder α] : ClosureOperator (Set α) := GaloisConnection.closureOperator <| DedekindMacNeilleConnection α


abbrev DedekindMacNeilleCompletion (α : Type*) [PartialOrder α] := (DedekindMacNeilleClosureOperator α).Closeds


instance {α : Type*} [PartialOrder α] : CompleteLattice (DedekindMacNeilleCompletion α) := inferInstance

instance {α : Type*} [LinearOrder α] : IsTotal (DedekindMacNeilleCompletion α) instCompleteLatticeDedekindMacNeilleCompletion.le := by
  refine { total := ?_ }
  intro a b
  rcases a with ⟨A, hA⟩
  rcases b with ⟨B, hB⟩
  simp only [Subtype.mk_le_mk, Set.le_eq_subset]
  apply or_iff_not_imp_left.2
  intro h1
  rcases Set.not_subset_iff_exists_mem_not_mem.1 h1 with ⟨a₀,ha₀⟩
  intro b hb
  rw [← hB] at hb
  simp only [GaloisConnection.lowerAdjoint_toFun, OrderDual.ofDual_toDual] at hb
  by_contra hc
  rw [← hA] at hc
  simp only [GaloisConnection.lowerAdjoint_toFun, OrderDual.ofDual_toDual] at hc
  unfold lowerBounds at hc
  simp only [Set.mem_setOf_eq, not_forall, Classical.not_imp, not_le] at hc
  rcases hc with ⟨a',ha'1,ha'2⟩
  have hhb : b ∈ upperBounds A := upperBounds_mono (fun ⦃a⦄ a ↦ a) (le_of_lt ha'2) ha'1
  have hB : B = lowerBounds (upperBounds B) := by
    nth_rw 1 [← hB]
    simp only [GaloisConnection.lowerAdjoint_toFun, OrderDual.ofDual_toDual]
  exact ha₀.2 <| hB ▸ lowerBounds_mono (fun ⦃a⦄ a ↦ a) (hhb ha₀.1) hb

--open Classical

noncomputable instance {α : Type*} [LinearOrder α] : LinearOrder (DedekindMacNeilleCompletion α) := {
  instCompleteLatticeDedekindMacNeilleCompletion with
  le_total := instIsTotalDedekindMacNeilleCompletionLe.total
  toDecidableLE := Classical.decRel LE.le
  min_def a b := by
    by_cases h : a ≤ b
    · simp only [h, inf_of_le_left, ↓reduceIte]
    · simp only [h, ↓reduceIte, inf_eq_right]
      simpa [h] using instIsTotalDedekindMacNeilleCompletionLe.total a b
  max_def a b := by
    by_cases h : a ≤ b
    · simp only [h, sup_of_le_right, ↓reduceIte]
    · simp only [h, ↓reduceIte, sup_eq_left]
      simpa only [h, false_or] using instIsTotalDedekindMacNeilleCompletionLe.total a b
  }

noncomputable instance {α : Type*} [LinearOrder α] : CompleteLinearOrder (DedekindMacNeilleCompletion α) :=
  {instLinearOrderDedekindMacNeilleCompletion , LinearOrder.toBiheytingAlgebra, instCompleteLatticeDedekindMacNeilleCompletion with}


def coe' {α : Type*} [PartialOrder α] : α ↪o DedekindMacNeilleCompletion α := by
  have inj: ∀ x : α, (DedekindMacNeilleClosureOperator α).IsClosed (Set.Iic x) := fun x ↦ Set.ext fun y ↦ ⟨fun hy ↦ hy (by simp only [upperBounds,
    GaloisConnection.lowerAdjoint_toFun, Set.mem_Iic, OrderDual.ofDual_toDual, Set.mem_setOf_eq,
    imp_self, implies_true]),fun hy x_1 ha ↦ ha hy⟩
  have : Function.Injective fun x ↦ (⟨Set.Iic x,inj x⟩ : DedekindMacNeilleCompletion α) := by
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact le_antisymm (hab ▸ Set.right_mem_Iic).out (hab.symm ▸ Set.right_mem_Iic).out
  use ⟨fun x ↦ ⟨Set.Iic x, inj x⟩,this⟩
  simp only [Function.Embedding.coeFn_mk, Subtype.mk_le_mk, Set.le_eq_subset, Set.Iic_subset_Iic,
    implies_true]


instance {α : Type*} [PartialOrder α]: Coe α (DedekindMacNeilleCompletion α) := ⟨coe'.toFun⟩


theorem DedekindMacNeilleCompletion_minimality {α : Type*} [PartialOrder α] {β : Type*} [CompleteLattice β] (f : α ↪o β) : ∃ f' : DedekindMacNeilleCompletion α ↪o β, f = f' ∘ coe' := by
  let g := fun x : DedekindMacNeilleCompletion α ↦ sSup <| lowerBounds <| upperBounds <| f '' x.val
  have : ∀ (A B : DedekindMacNeilleCompletion α), g A ≤ g B ↔ A ≤ B := by
    refine fun A B ↦ ⟨?_,?_⟩
    · intro h
      by_contra!
      rcases (Set.not_subset.1 this) with ⟨a, haA, haB⟩
      have : ∃ u ∈ upperBounds B, ¬ a ≤ u := by
        by_contra!
        exact haB ((ClosureOperator.IsClosed.closure_eq B.property) ▸ this)
      refine (fun w ↦ this.choose_spec.2 (f.map_rel_iff'.1 w)) ?_
      have h₁ : f a ≤ g A := le_sSup fun u hu ↦ hu (Exists.intro a ⟨haA, rfl⟩)
      have h₂ : g B ≤ f (this.choose) := by
        refine sSup_le fun y hy ↦ hy ?_
        simp only [upperBounds, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, OrderEmbedding.le_iff_le]
        exact this.choose_spec.1.out
      exact le_trans h₁ <| le_trans h h₂
    · intro h
      simp only [upperBounds, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        sSup_le_iff, g]
      exact fun y hy ↦ hy.out fun w hw ↦ le_sSup fun ⦃a⦄ a ↦ a w (h hw)
  refine ⟨⟨⟨g,fun x y h ↦ le_antisymm ((this x y).1 <| (le_antisymm_iff.1 h).1) ((this y x).1 <| (le_antisymm_iff.1 h).2)⟩,?_⟩,?_⟩
  · simp only [Function.Embedding.coeFn_mk, Subtype.forall, Subtype.mk_le_mk, Set.le_eq_subset, g]
    exact fun x hx y hy ↦ this ⟨x, hx⟩ ⟨y, hy⟩
  · refine funext fun x ↦ ?_
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, coe', Function.comp_apply, g]
    refine le_antisymm (le_sSup fun a ha ↦ ha.out <| Set.mem_image_of_mem f Set.right_mem_Iic) <| sSup_le fun _ hb ↦ hb ?_
    simp only [upperBounds, Set.mem_image, Set.mem_Iic, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, OrderEmbedding.le_iff_le, imp_self, implies_true,
      g]

--TODO: joint-dense, meet-dense
end DedekindMacNeille

end OrderTheory
