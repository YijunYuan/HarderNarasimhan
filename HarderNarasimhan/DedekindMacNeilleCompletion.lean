import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Closure


instance {α : Type} [PartialOrder α] (T : ClosureOperator (Set α)): CompleteLattice (ClosureOperator.Closeds T) where
  top :=⟨Set.univ,ClosureOperator.isClosed_iff_closure_le.mpr fun ⦃a⦄ a ↦ trivial⟩
  le_top A := fun ⦃a⦄ a ↦ trivial
  bot := ⟨T ∅, ClosureOperator.isClosed_closure T ∅⟩
  bot_le A := by
    intro a ha
    simp at *
    exact (ClosureOperator.IsClosed.closure_eq A.property) ▸ (T.monotone <| Set.empty_subset A.val) ha
  inf A B := ⟨A.val ∩ B.val,ClosureOperator.isClosed_iff_closure_le.mpr fun x hx ↦ (ClosureOperator.IsClosed.closure_eq A.property) ▸ (ClosureOperator.IsClosed.closure_eq B.property) ▸ ⟨(T.monotone <| Set.inter_subset_left) hx,(T.monotone <| Set.inter_subset_right) hx⟩⟩
  le_inf A B C h1 h2 := fun a ha ↦ ⟨h1 ha,h2 ha⟩
  inf_le_left A B := fun ⦃a⦄ b ↦ b.1
  inf_le_right A B := fun ⦃a⦄ b ↦ b.right
  sup A B := ⟨T (A.val ∪ B.val), ClosureOperator.isClosed_closure T (A.val ∪ B.val)⟩
  sup_le A B C h1 h2 := by
    intro a ha
    simp at *
    exact (ClosureOperator.IsClosed.closure_eq C.property) ▸ (T.monotone <| Set.union_subset h1 h2) ha
  le_sup_left := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq A.property).symm]
    exact ClosureOperator.monotone T <| Set.subset_union_left
  le_sup_right := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq B.property).symm]
    exact ClosureOperator.monotone T <| Set.subset_union_right
  sInf 𝒮 := by
    refine ⟨⋂ a ∈ 𝒮, a.val,ClosureOperator.isClosed_iff_closure_le.mpr fun x hx ↦ ?_⟩
    simp at *
    refine fun S hS hSb ↦ (ClosureOperator.IsClosed.closure_eq hS) ▸ T.monotone (fun x hx ↦ ?_) hx
    simp at hx
    exact hx S hS hSb
  le_sInf 𝒮 A hA := by
    intro x h
    simp at *
    exact fun S hS hSb ↦ hA S hS hSb h
  sInf_le 𝒮 A:= by
    intro hA x hx
    simp at *
    exact hx A.val A.prop hA
  sSup 𝒮 := ⟨T (⋃ a ∈ 𝒮, a.val),ClosureOperator.isClosed_closure T (⋃ a ∈ 𝒮, a.val)⟩
  le_sSup 𝒮 A hA:= fun x hx ↦ ClosureOperator.monotone T (Set.subset_biUnion_of_mem hA) <| (ClosureOperator.IsClosed.closure_eq A.property).symm ▸ hx
  sSup_le 𝒮 A hA := by
    intro x hx
    simp
    refine (ClosureOperator.IsClosed.closure_eq A.property) ▸ ClosureOperator.monotone T (fun y hy ↦ ?_) hx
    simp at hy
    exact Exists.casesOn hy fun S h ↦ And.casesOn h fun left hSb ↦ Exists.casesOn left fun hS hP ↦ hA ⟨S, hS⟩ hP hSb


section DedekindMacNeille
lemma DedekindMacNeilleConnection (α : Type) [PartialOrder α] : GaloisConnection (fun A ↦ (OrderDual.toDual (upperBounds A))) (fun A : (Set α)ᵒᵈ ↦ lowerBounds A.ofDual) := fun _ _ ↦ ⟨fun h _ ha ⦃_⦄ a_3 ↦ h a_3 ha, fun h _ ha ⦃_⦄ a_2 ↦ h a_2 ha⟩


def DedekindMacNeilleClosureOperator (α : Type) [PartialOrder α] : ClosureOperator (Set α) := GaloisConnection.closureOperator <| DedekindMacNeilleConnection α


abbrev DedekindMacNeilleCompletion (α : Type) [PartialOrder α] := (DedekindMacNeilleClosureOperator α).Closeds


instance {α : Type} [PartialOrder α] : CompleteLattice (DedekindMacNeilleCompletion α) := inferInstance


def coe' {α : Type} [PartialOrder α] : α ↪o DedekindMacNeilleCompletion α := by
  have inj: ∀ x : α, (DedekindMacNeilleClosureOperator α).IsClosed (Set.Iic x) := fun x ↦ Set.ext fun y ↦ ⟨fun hy ↦ hy (by simp [upperBounds]),fun hy x_1 ha ↦ ha hy⟩
  have : Function.Injective fun x ↦ (⟨Set.Iic x,inj x⟩ : DedekindMacNeilleCompletion α) := by
    intro a b hab
    simp at hab
    exact le_antisymm (hab ▸ Set.right_mem_Iic).out (hab.symm ▸ Set.right_mem_Iic).out
  use ⟨fun x ↦ ⟨Set.Iic x, inj x⟩,this⟩
  simp


instance {α : Type} [PartialOrder α]: Coe α (DedekindMacNeilleCompletion α) := ⟨coe'.toFun⟩




theorem universal_property {α : Type} [PartialOrder α] (β : Type) [CompleteLattice β] (f : α ↪o β) : ∃ f' : DedekindMacNeilleCompletion α ↪o β, f = f' ∘ coe' := by
  let g := fun x : DedekindMacNeilleCompletion α ↦ sSup <| lowerBounds <| upperBounds <| f '' x.val
  have : ∀ (a b : DedekindMacNeilleCompletion α), g a ≤ g b ↔ a ≤ b := by
    intro a b
    constructor
    · intro h

      sorry
    · intro h
      simp [g,upperBounds]
      exact fun y hy ↦ hy.out fun w hw ↦ le_sSup fun ⦃a⦄ a ↦ a w (h hw)
  refine ⟨⟨⟨g,?_⟩,?_⟩,?_⟩
  · exact fun x y h ↦ le_antisymm ((this x y).1 <| (le_antisymm_iff.1 h).1) ((this y x).1 <| (le_antisymm_iff.1 h).2)
  · simp
    exact fun x hx y hy ↦ this ⟨x, hx⟩ ⟨y, hy⟩
  · refine funext fun x ↦ ?_
    simp [g,coe']
    apply le_antisymm
    · exact le_sSup fun a ha ↦ ha.out <| Set.mem_image_of_mem f Set.right_mem_Iic
    · refine sSup_le fun _ hb ↦ hb ?_
      simp [upperBounds]

--TODO: joint-dense, meet-dense
end DedekindMacNeille
