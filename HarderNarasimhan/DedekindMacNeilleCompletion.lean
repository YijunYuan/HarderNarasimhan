import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Closure


instance {α : Type} [PartialOrder α] (T : ClosureOperator (Set α)): CompleteLattice (ClosureOperator.Closeds T) where
  top :=⟨Set.univ,ClosureOperator.isClosed_iff_closure_le.mpr fun ⦃a⦄ a ↦ trivial⟩
  le_top A := fun ⦃a⦄ a ↦ trivial
  bot := by
    use T ∅
    exact ClosureOperator.isClosed_closure T ∅
  bot_le A := by
    intro a ha
    simp at *
    rw [← ClosureOperator.IsClosed.closure_eq A.property]
    exact (T.monotone <| Set.empty_subset A.val) ha
  inf A B := by
    use A.val ∩ B.val
    refine ClosureOperator.isClosed_iff_closure_le.mpr ?_
    intro x hx
    simp [*] at *
    rw [← ClosureOperator.IsClosed.closure_eq A.property,← ClosureOperator.IsClosed.closure_eq B.property]
    exact ⟨(T.monotone <| Set.inter_subset_left) hx,(T.monotone <| Set.inter_subset_right) hx⟩
  le_inf A B C h1 h2 := by
    exact fun a ha ↦ ⟨h1 ha,h2 ha⟩
  inf_le_left A B := by
    intro a b
    exact b.1
  inf_le_right A B := by
    intro a b
    exact b.2
  sup A B := ⟨T (A.val ∪ B.val), ClosureOperator.isClosed_closure T (A.val ∪ B.val)⟩
  sup_le A B C h1 h2 := by
    intro a ha
    simp at *
    rw [← ClosureOperator.IsClosed.closure_eq C.property]
    exact (T.monotone <| Set.union_subset h1 h2) ha
  le_sup_left := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq A.property).symm]
    exact ClosureOperator.monotone T <| Set.subset_union_left
  le_sup_right := by
    intro A B
    nth_rw 1 [Subtype.coe_eq_of_eq_mk (ClosureOperator.IsClosed.closure_eq B.property).symm]
    exact ClosureOperator.monotone T <| Set.subset_union_right
  sInf 𝒮 := by
    use ⋂ a ∈ 𝒮, a.val
    refine ClosureOperator.isClosed_iff_closure_le.mpr ?_
    intro x hx
    simp at *
    intro S hS hSb
    rw [← ClosureOperator.IsClosed.closure_eq hS]
    have : ⋂ a ∈ 𝒮, a.val ⊆ S := by
      intro x hx
      simp at hx
      exact hx S hS hSb
    exact T.monotone this hx
  le_sInf 𝒮 A hA := by
    intro x h
    simp at *
    intro S hS hSb
    exact hA S hS hSb h
  sInf_le 𝒮 A:= by
    intro hA x hx
    simp at *
    exact hx A.val A.prop hA
  sSup 𝒮 := ⟨T (⋃ a ∈ 𝒮, a.val),ClosureOperator.isClosed_closure T (⋃ a ∈ 𝒮, a.val)⟩
  le_sSup 𝒮 A hA:= by
    intro x hx
    simp at *
    rw [← ClosureOperator.IsClosed.closure_eq A.property] at hx
    exact ClosureOperator.monotone T (Set.subset_biUnion_of_mem hA) hx
  sSup_le 𝒮 A hA := by
    intro x hx
    simp
    rw [← ClosureOperator.IsClosed.closure_eq A.property]
    refine ClosureOperator.monotone T ?_ hx
    intro y hy
    simp at hy
    rcases hy with ⟨S, ⟨hS, hP⟩, hSb⟩
    exact hA ⟨S, hS⟩ hP hSb


namespace DedekindMacNeille

lemma Conn (α : Type) [PartialOrder α] : GaloisConnection (fun A ↦ (OrderDual.toDual (upperBounds A))) (fun A : (Set α)ᵒᵈ ↦ lowerBounds A.ofDual) := fun _ _ ↦ ⟨fun h _ ha ⦃_⦄ a_3 ↦ h a_3 ha, fun h _ ha ⦃_⦄ a_2 ↦ h a_2 ha⟩

def Cl (α : Type) [PartialOrder α] : ClosureOperator (Set α) := GaloisConnection.closureOperator <| Conn α

abbrev DedekindMacNeilleCompletion (α : Type) [PartialOrder α] := (Cl α).Closeds

instance {α : Type} [PartialOrder α] : CompleteLattice (DedekindMacNeilleCompletion α) := inferInstance


def coe' {α : Type} [PartialOrder α] : α ↪o DedekindMacNeilleCompletion α := by
  have : Function.Injective fun x ↦ (Cl α).toCloseds {x} := by
    intro x y hxy
    simp at hxy
    apply Subtype.coe_inj.2 at hxy
    have : (Cl α) {x} = (Cl α) {y} := hxy
    unfold Cl at this
    simp at this
    have h : x ∈ lowerBounds (Set.Ici y) := this ▸ fun ⦃a⦄ a ↦ a
    have h' : y ∈ lowerBounds (Set.Ici x) := this ▸ (fun ⦃a⦄ a ↦ a)
    exact le_antisymm (h.out <| Set.mem_Ici.2 <| le_refl y) (h'.out <| Set.mem_Ici.2 <| le_refl x)
  use ⟨fun x ↦ (Cl α).toCloseds {x},this⟩
  intro a b
  simp
  constructor
  · intro h
    have : a ∈ lowerBounds (Set.Ici b) := by
      unfold ClosureOperator.toCloseds at h
      simp at h
      unfold Cl at h
      simp at h
      exact h
    exact this.out Set.left_mem_Ici
  · intro h x hx
    have h' : x ∈ (Cl α) {a} := hx.out
    unfold Cl at h'
    simp at h'
    exact fun ⦃_⦄ a_1 ↦ ((lowerBounds_mono_set <| Set.Ici_subset_Ici.mpr h) h') (a_1 rfl)

instance {α : Type} [PartialOrder α]: Coe α (DedekindMacNeilleCompletion α) := ⟨coe'.toFun⟩

theorem universal_property {α : Type} [PartialOrder α] (β : Type) [CompleteLattice β] (f : α ↪o β) : ∃ f' : DedekindMacNeilleCompletion α ↪o β, f = f' ∘ coe' := by admit

--TODO: joint-dense, meet-dense

end DedekindMacNeille
