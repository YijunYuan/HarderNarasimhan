import HarderNarasimhan.Semistability.Results
import Mathlib.Data.Real.Basic

namespace HarderNarasimhan

namespace impl

noncomputable def prop4d1₁_seq {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩)
(h₃ : {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩}.Nonempty)
(k : ℕ)
: {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩} :=
  match k with
  | 0 => ⟨h₃.choose,h₃.choose_spec⟩
  | k + 1 => by
    let prop4d1₁_seqkp1 := (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose_spec (prop4d1₁_seq μ h₁ h₂ h₃ k) (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose
    use prop4d1₁_seqkp1.choose
    have h''' := prop4d1₁_seqkp1.choose_spec.choose_spec
    have h' : prop4d1₁_seqkp1.choose < ⊤ := by
      by_contra! hcon
      simp only [Set.mem_setOf_eq, not_lt_top_iff.mp hcon, le_refl, not_true_eq_false] at h'''
    by_contra!
    simp only [Set.mem_setOf_eq, not_exists, not_forall, not_not] at this
    rcases this h' with ⟨xA,⟨hxA,hh⟩⟩
    have hhh : ∀ (xB : ℒ) (x_1 : xA < xB), μ ⟨(xA, xB), x_1⟩ ≤ μ ⟨(prop4d1₁_seq μ h₁ h₂ h₃ k, ⊤), (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.choose⟩ := fun xB hAB ↦ le_trans (hh xB hAB) <| Or.resolve_left (h₂ ⟨(prop4d1₁_seq μ h₁ h₂ h₃ k, prop4d1₁_seqkp1.choose), prop4d1₁_seqkp1.choose_spec.choose⟩ h') h'''
    rcases (prop4d1₁_seq μ h₁ h₂ h₃ k).prop.out.choose_spec xA hxA with ⟨xB,⟨hAB,con⟩⟩
    exact con (hhh xB hAB)


lemma prop4d1_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : sInf {x | ∃ x_1, ∃ (hx : x_1 < ⊤), μ ⟨(x_1, ⊤), hx⟩ = x} = μmin μ TotIntvl := by
    refine congrArg sInf <| Set.ext fun x ↦ ?_
    constructor
    · rintro ⟨w, hw, hw'⟩
      use w, ⟨in_TotIntvl w, ne_top_of_lt hw⟩
    · rintro ⟨w,hw,hw'⟩
      use w, lt_top_iff_ne_top.2 hw.2


lemma prop4d1₁ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) :
μAstar μ = μmin μ TotIntvl := by
  rw [← prop4d1_helper]
  have : ∀ yA : ℒ, (hyA : yA < ⊤) → ∃ xA : ℒ, xA < ⊤ ∧ (∀ xB : ℒ, (hAB : xA < xB) → μ ⟨(xA,xB), hAB⟩ ≤ μ ⟨(yA,⊤), hyA⟩) := by
    by_contra!
    have : {YA : ℒ | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩}.Nonempty := this
    have hsmf : StrictMono (fun n ↦ prop4d1₁_seq μ h₁ h₂ this n) := strictMono_nat_of_lt_succ <| fun n ↦ ((prop4d1₁_seq μ h₁ h₂ this n).prop.out.choose_spec (prop4d1₁_seq μ h₁ h₂ this n) (prop4d1₁_seq μ h₁ h₂ this n).prop.out.choose).choose_spec.choose
    have hfinal : ∀ n : ℕ, ¬ μ ⟨((prop4d1₁_seq μ h₁ h₂ this n),(prop4d1₁_seq μ h₁ h₂ this (n+1))),hsmf (Nat.lt_add_one n)⟩ ≤ μ ⟨((prop4d1₁_seq μ h₁ h₂ this n),⊤),lt_of_lt_of_le (hsmf (Nat.lt_add_one n)) le_top⟩ := fun n ↦ ((prop4d1₁_seq μ h₁ h₂ this n).prop.out.choose_spec (prop4d1₁_seq μ h₁ h₂ this n) (prop4d1₁_seq μ h₁ h₂ this n).prop.out.choose).choose_spec.choose_spec
    rcases h₁ (fun n ↦ prop4d1₁_seq μ h₁ h₂ this n) hsmf with ⟨N,hN⟩
    exact (hfinal N) hN
  refine le_antisymm ?_ ?_
  · apply le_sInf
    rintro y ⟨yA, hyA, h⟩
    rcases this yA hyA with ⟨xA, hxA, h'⟩
    have : μmax μ ⟨(xA,⊤),hxA⟩ ∈ {μmax μ ⟨(a , ⊤),(lt_of_le_of_ne ha.1.2 ha.2)⟩ | (a : ℒ) (ha : InIntvl TotIntvl a ∧ a ≠ ⊤)} := by
      refine Set.mem_setOf.mpr ?_
      use xA, ⟨in_TotIntvl xA,ne_top_of_lt hxA⟩
    refine h.symm ▸ (sInf_le_of_le this <| sSup_le ?_)
    rintro _ ⟨xB,⟨hxB,hxB'⟩⟩
    exact hxB' ▸ h' xB (lt_of_le_of_ne hxB.1.1 hxB.2)
  · apply le_sInf
    rintro t ⟨x, hx, h⟩
    have : μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩ ∈  {x | ∃ x_1, ∃ (hx : x_1 < ⊤), μ ⟨(x_1, ⊤), hx⟩ = x} := by
      refine Set.mem_setOf.mpr ?_
      use x, lt_top_iff_ne_top.2 hx.2
    refine h.symm ▸ (sInf_le_of_le this <| Set.mem_setOf.mpr <| le_sSup ?_)
    use ⊤, ⟨⟨le_top,le_top⟩,hx.2⟩


lemma prop4d1₂ (ℒ : Type*) [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
(S : Type*) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) :
μAstar μ ≤ μBstar μ := by
  rw [prop4d1₁ ℒ S μ h₁ h₂]
  apply le_sSup
  use ⊤, ⟨⟨bot_le,le_rfl⟩,ne_of_lt bot_lt_top⟩


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] : Coe ({p :ℒ × ℒ // p.1 < p.2}) ({p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) where
  coe p := ⟨(p.val.2, p.val.1), p.prop⟩


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] : Coe ({p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ({p :ℒ × ℒ // p.1 < p.2}) where
  coe p := ⟨(p.val.2, p.val.1), p.prop⟩


instance {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S] : Coe ({p :ℒ × ℒ // p.1 < p.2} → S) ({p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) where
  coe f := fun p ↦ f p


lemma fine {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {S : Type*} [CompleteLattice S] (μ : {p :ℒ × ℒ // p.1 < p.2} → S) : ∀ I : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}, μ ⟨(I.val.2.ofDual,I.val.1.ofDual),I.prop⟩ = OrderDual.ofDual ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) I) := fun _ ↦ rfl


lemma h₁_dual_of_h₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S} (h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩) :
(∀ x : ℕ → ℒᵒᵈ, (smf : StrictMono x) → ∃ N : ℕ, @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩)  ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)) := by
  intro xd smf
  rcases (h₁ (fun n ↦ (xd n).ofDual) fun _ _ hab ↦ smf hab) with ⟨N, hN⟩
  have := fine μ ⟨(xd N, ⊤), lt_of_lt_of_le (smf (Nat.lt_add_one N)) le_top⟩
  simp only [OrderDual.ofDual_top] at this
  rw [this,fine μ ⟨(xd N, xd (N + 1)), smf (Nat.lt_add_one N)⟩] at hN
  use N, OrderDual.ofDual_le_ofDual.1 hN


lemma h₂_dual_of_h₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ] {S : Type*} [CompleteLattice S] {μ : {p :ℒ × ℒ // p.1 < p.2} → S}
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩) :
∀ z : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}, (hz :z.val.2 < ⊤) → @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) z) ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) ∨ @LE.le Sᵒᵈ (OrderDual.instLE S) ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) ⟨(z.val.2,⊤),hz⟩) ((↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) := by
  intro z hz
  exact h₂ z hz


lemma dualμAstar_eq_μBstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
OrderDual.ofDual <| μAstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦ OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μBstar μ
:= by
  simp only [μAstar, μA, sInf, ne_eq, OrderDual.exists, μBstar, μB]
  refine congrArg (@sSup S _) <| Set.ext fun x ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    use a, ⟨in_TotIntvl a,Ne.symm ha.2⟩
    refine ha' ▸ (congrArg sInf <| Set.ext fun r ↦ ?_)
    constructor
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
  · rintro ⟨a, ha, ha'⟩
    use a, ⟨in_TotIntvl (OrderDual.toDual a),Ne.symm ha.2⟩
    refine ha' ▸ (congrArg sSup <| Set.ext fun r ↦ ?_)
    constructor
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩


lemma dualμBstar_eq_μAstar {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
OrderDual.ofDual <| μBstar (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦ OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) = μAstar μ
:= by
  simp only [μBstar, μB, sSup, ne_eq, OrderDual.exists, μAstar, μA]
  refine congrArg (@sInf S _) <| Set.ext fun x ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    use a, ⟨in_TotIntvl a,Ne.symm ha.2⟩
    refine ha' ▸ (congrArg sSup <| Set.ext fun r ↦ ?_)
    constructor
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
  · rintro ⟨a, ha, ha'⟩
    use a, ⟨in_TotIntvl (OrderDual.toDual a),Ne.symm ha.2⟩
    refine ha'.symm ▸ (congrArg sInf <| Set.ext fun r ↦ ?_)
    constructor
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩
    · rintro ⟨b, hb, hb'⟩
      exact ⟨b, ⟨⟨hb.1.2,hb.1.1⟩,Ne.symm hb.2⟩, hb'.symm ▸ rfl⟩


lemma prop4d3_helper {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : sSup {μ ⟨(⊥, y),hy⟩ | (y : ℒ) (hy : ⊥ < y) } = μmax μ TotIntvl := by
    refine congrArg sSup <| Set.ext fun x ↦ ?_
    constructor
    · rintro ⟨w, hw, hw'⟩
      use w, ⟨in_TotIntvl w, ne_of_lt hw⟩
    · rintro ⟨w,hw,hw'⟩
      use w, bot_lt_iff_ne_bot.2 <| Ne.symm hw.2


lemma prop4d3₁ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩) :
μBstar μ = μmax μ TotIntvl := by
  have := prop4d1₁ ℒᵒᵈ Sᵒᵈ (fun (p : {p : ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2}) ↦ OrderDual.toDual <| μ ⟨(p.val.2, p.val.1), p.prop⟩) (h₁_dual_of_h₁ h₁) (h₂_dual_of_h₂ h₂)
  rw [← prop4d1_helper] at this
  rw [← prop4d3_helper]
  simp only [OrderDual.exists] at this
  rw [← dualμAstar_eq_μBstar, this]
  refine congrArg sSup <| Set.ext fun r ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    use a, ha, ha'
  · rintro ⟨a, ha, ha'⟩
    use a, ha, ha'


lemma prop4d3₂ {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩) :
μAstar μ ≤ μBstar μ := (dualμAstar_eq_μBstar μ) ▸ (dualμBstar_eq_μAstar μ) ▸ prop4d1₂ ℒᵒᵈ Sᵒᵈ (↑μ : {p :ℒᵒᵈ × ℒᵒᵈ // p.1 < p.2} → Sᵒᵈ) (h₁_dual_of_h₁ h₁) (h₂_dual_of_h₂ h₂)


lemma rmk4d4 {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(r : ℒ → ℝ) (hr₁ : Monotone r) (hr₂ : IsWellOrder (Set.range r) (· < ·))
(h : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, r z.val.1 = r z.val.2 → μ z = ⊤) :
∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩ := by
  intro x saf
  let W : Set (Set.range r) := {s : Set.range r | ∃ N : ℕ, s = r (x N)}
  have hW : W.Nonempty := by
    use ⟨(r (x 0)), Set.mem_range_self (x 0)⟩
    refine Set.mem_setOf.mpr ?_
    use 0
  have : ∃ N : ℕ, r (x N) = r (x (N + 1)) := by
    let n := (hr₂.wf.has_min W hW).choose_spec.1.out.choose
    use n
    have : ⟨r (x (n + 1)),Set.mem_range_self (x (n + 1))⟩ ∈ W := by
      refine Set.mem_setOf.mpr ?_
      use n + 1
    exact eq_of_le_of_not_lt' (hr₁ <| le_of_lt <| saf <| Nat.lt_add_one n) <| (hr₂.wf.has_min W hW).choose_spec.1.out.choose_spec ▸ (hr₂.wf.has_min W hW).choose_spec.2 ⟨r (x (n + 1)),Set.mem_range_self (x (n + 1))⟩ this
  use this.choose, (h ⟨(x (this.choose+1), x this.choose), saf <| Nat.lt_add_one this.choose⟩ this.choose_spec.symm) ▸ le_top

end impl

end HarderNarasimhan
