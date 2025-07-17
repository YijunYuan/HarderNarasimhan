import HarderNarasimhan.NashEquilibrium.Defs
import HarderNarasimhan.FirstMoverAdvantage.Impl
import HarderNarasimhan.FirstMoverAdvantage.Defs
import HarderNarasimhan.SlopeLike.Defs
import HarderNarasimhan.Semistability.Translation
import Mathlib.Tactic.TFAE
import Mathlib.Data.List.TFAE


namespace impl

lemma rmk4d10₀ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
∀ I : {p :ℒ × ℒ // p.1 < p.2}, μmin μ I ≤ μ I ∧ μ I ≤ μmax μ I := by
  intro I
  constructor
  · apply sInf_le
    use I.val.1, ⟨⟨le_rfl,le_of_lt I.prop⟩,ne_of_lt I.prop⟩
  · apply le_sSup
    use I.val.2, ⟨⟨le_of_lt I.prop,le_rfl⟩,ne_of_lt I.prop⟩


lemma rmk4d10₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
μBstar μ ≤ μAstar μ ↔ ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) → μmin μ ⟨(⊥,y),hy⟩ ≤ μmax μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx⟩ := by
  constructor
  · intro h x hx y hy
    simp [μAstar,μBstar] at h
    unfold μA at h
    unfold μB at h
    apply sSup_le_iff.1 at h
    simp [le_sInf_iff.1] at h
    refine (((fun (x : ℒ) (hx : ¬ ⊥ = x) ↦ h (μmin μ ⟨(⊥, x), bot_lt_iff_ne_bot.2 (by tauto)⟩) <| x) y <| ne_of_lt hy) ⟨in_TotIntvl y,by aesop⟩ <| rfl) (μmax μ ⟨(x, ⊤), lt_top_iff_ne_top.2 hx⟩) x ⟨in_TotIntvl x, hx⟩ rfl
  · refine fun h ↦ sSup_le_iff.2 ?_
    simp
    refine fun b x hx h' ↦ h' ▸ le_sInf_iff.2 ?_
    simp
    exact fun _ x' _ h'' ↦ h'' ▸ h x' (by tauto) x _


lemma rmk4d10₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : prop_4_1_cond₁ μ) (h₂ : prop_4_1_cond₂ μ):
NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊥) → μmin μ ⟨(⊥,y),bot_lt_iff_ne_bot.2 hy⟩ ≤ μmin μ TotIntvl := by
  constructor
  · intro h y hy
    unfold NashEquilibrium at h
    rw [impl.prop4d1₁ ℒ S μ h₁ h₂] at h
    simp [μBstar,TotIntvl,μB] at h
    unfold TotIntvl
    rw [h]
    apply le_sSup
    use y, ⟨in_TotIntvl y,Ne.symm hy⟩
  · intro h
    unfold NashEquilibrium
    rw [impl.prop4d1₁ ℒ S μ h₁ h₂]
    simp [μBstar,μB]
    apply eq_of_le_of_le
    · apply le_sSup
      unfold TotIntvl
      use ⊤, ⟨in_TotIntvl ⊤, bot_ne_top⟩
    · apply sSup_le
      rintro b ⟨h1,⟨h2,h3⟩⟩
      exact h3 ▸ (h h1 <| Ne.symm h2.2)


lemma rmk4d10₃ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : prop_4_3_cond₁ μ) (h₂ : prop_4_3_cond₂ μ):
NashEquilibrium μ ↔ ∀ y : ℒ, (hy : y ≠ ⊤) → μmax μ TotIntvl ≤ μmax μ ⟨(y,⊤),lt_top_iff_ne_top.2 hy⟩ := by
  constructor
  · intro h y hy
    unfold NashEquilibrium at h
    rw [impl.prop4d3₁ μ h₁ h₂] at h
    simp [μBstar,TotIntvl,μB] at h
    unfold TotIntvl
    rw [← h]
    unfold μAstar μA
    apply sInf_le
    use y, ⟨in_TotIntvl y,hy⟩
  · intro h
    unfold NashEquilibrium
    rw [impl.prop4d3₁ μ h₁ h₂]
    simp [μAstar,μA]
    apply eq_of_le_of_le
    · apply sInf_le
      unfold TotIntvl
      use ⊥, ⟨in_TotIntvl ⊥, bot_ne_top⟩
    · apply le_sInf
      rintro b ⟨h1,⟨h2,h3⟩⟩
      exact h3 ▸ (h h1 h2.2)


lemma prop4d11₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
μmin μ TotIntvl = μmax μ TotIntvl → μBstar μ ≤ μAstar μ := by
  have h₁ : μBstar μ ≤ μmax μ TotIntvl := by
    unfold μBstar μB μmax TotIntvl
    apply sSup_le
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    refine hb3 ▸ le_trans (rmk4d10₀ μ ⟨(⊥,hb1), bot_lt_iff_ne_bot.2 <| Ne.symm hb2.2⟩).1 <| le_sSup ?_
    use hb1, ⟨in_TotIntvl hb1, hb2.2⟩
  have h₂ : μmin μ TotIntvl ≤ μAstar μ := by
    unfold μAstar μA μmin TotIntvl
    apply le_sInf
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    refine hb3 ▸ le_trans (sInf_le ?_) (rmk4d10₀ μ ⟨(hb1,⊤), lt_top_iff_ne_top.2 <| hb2.2⟩).2
    use hb1, ⟨in_TotIntvl hb1, hb2.2⟩
  exact fun h ↦ le_trans h₁ (h ▸ h₂)


lemma prop4d11₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : prop_4_1_cond₁ μ) (h₂ : prop_4_1_cond₂ μ)
(h₁' : prop_4_3_cond₁ μ) (h₂' : prop_4_3_cond₂ μ):
μBstar μ ≤ μAstar μ → μmin μ TotIntvl = μmax μ TotIntvl := fun h ↦ eq_of_le_of_le (le_trans (rmk4d10₀ μ TotIntvl).1 (rmk4d10₀ μ ⟨(⊥,⊤),bot_lt_top⟩).2) <| (impl.prop4d3₁ μ h₁' h₂') ▸ (impl.prop4d1₁ ℒ S μ h₁ h₂) ▸ h


lemma prop4d12 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
μmax μ TotIntvl = μ TotIntvl → μmin μ TotIntvl = μmax μ TotIntvl := by
  refine fun h' ↦ h' ▸ eq_of_le_of_le (rmk4d10₀ μ TotIntvl).1 ?_
  · apply le_sInf
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    rw [← hb3]
    by_cases hbot : hb1 = ⊥
    · simp [hbot]
      exact le_rfl
    refine Or.resolve_left (h hb1 <| ⟨hbot,hb2.2⟩) ?_
    rw [not_not]
    refine h' ▸ (le_sSup ?_)
    use hb1, ⟨in_TotIntvl hb1, Ne.symm hbot⟩
    rfl


lemma rmk4d13 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ):
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → ¬ μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩ := by
  intro x hx
  have := (hμ ⊥ x ⊤ ⟨bot_lt_iff_ne_bot.2 hx.1,lt_top_iff_ne_top.2 hx.2⟩).2.2.1
  cases' this with this this
  · exact Or.inl <| not_le_of_lt this
  · exact Or.inr this


lemma prop4d14 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h : ∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩) :
μmin μ TotIntvl = μ TotIntvl → μmax μ TotIntvl = μmin μ TotIntvl := by
  refine fun h' ↦ h' ▸ eq_of_le_of_le ?_ (rmk4d10₀ μ TotIntvl).2
  · apply sSup_le
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    rw [← hb3]
    by_cases htop : hb1 = ⊤
    · simp [htop]
      exact le_rfl
    refine Or.resolve_right (h hb1 ⟨by tauto,htop⟩) ?_
    rw [not_not]
    refine h' ▸ (sInf_le ?_)
    use hb1, ⟨in_TotIntvl hb1, htop⟩
    rfl


lemma rmk4d15 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ):
∀ x : ℒ, (hx : x ≠ ⊥ ∧ x ≠ ⊤) → μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx.1⟩ ≤ μ TotIntvl ∨ ¬ μ TotIntvl ≤ μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩ := by
  intro x hx
  have := (hμ ⊥ x ⊤ ⟨bot_lt_iff_ne_bot.2 hx.1,lt_top_iff_ne_top.2 hx.2⟩).1
  cases' this with this this
  · exact Or.inl this
  · exact Or.inr <| not_le_of_lt this


lemma prop4d16₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ):
List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl
  ] := by
  tfae_have 1 → 3 := prop4d12 μ (rmk4d13 μ hμ)
  tfae_have 2 → 3 := fun h ↦ (prop4d14 μ (rmk4d15 μ hμ) h).symm
  tfae_have 3 → 1 := by
    intro h
    have := h ▸ rmk4d10₀ μ TotIntvl
    exact eq_of_le_of_le this.1 this.2
  tfae_have 3 → 2 := by
    intro h
    have := h.symm ▸ rmk4d10₀ μ TotIntvl
    exact eq_of_le_of_le this.1 this.2
  tfae_finish


lemma prop4d16₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ)
(h₁ : prop_4_1_cond₁ μ) (h₂ : prop_4_3_cond₁ μ) :
μmin μ TotIntvl = μmax μ TotIntvl ↔ NashEquilibrium μ := by
  have : ∀ (z : { p : ℒ × ℒ // p.1 < p.2 }) (hz : z.val.2 < ⊤), μ z ≤ μ ⟨(z.val.1, ⊤), lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2, ⊤), hz⟩ ≤ μ ⟨(z.val.1, ⊤), lt_trans z.prop hz⟩ := by
    intro z hz
    cases' (hμ z.val.1 z.val.2 ⊤ ⟨z.prop, hz⟩).1 with this this
    · exact Or.inl this
    · exact Or.inr <| le_of_lt this
  refine ⟨fun h ↦ eq_of_le_of_le (impl.prop4d1₂ ℒ S μ h₁ this) <| prop4d11₁ μ h,fun h ↦ prop4d11₂ μ h₁ this h₂ (fun z hz ↦ ?_) h.symm.le⟩
  cases' (hμ ⊥ z.val.1 z.val.2 ⟨hz,z.prop⟩).2.2.1 with this this
  · exact Or.inr <| le_of_lt this
  · exact Or.inl <| this


lemma prop4d18₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : semistable μ) : μBstar μ ≤ μAstar μ := by
  rw [semistable_iff] at hμ
  have : sSup {μA μ ⟨(⊥,x),hx⟩ | (x : ℒ) (hx : ⊥ < x)} ≤ μAstar μ := by
    apply sSup_le
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    have := hb3 ▸ hμ.out.choose_spec.choose_spec.1 hb1 (in_TotIntvl hb1) (Ne.symm <| bot_lt_iff_ne_bot.1 hb2)
    aesop
  refine le_trans (sSup_le_sSup_of_forall_exists_le ?_) this
  rintro x ⟨hx1,⟨hx2,hx3⟩⟩
  use μA μ ⟨(⊥,hx1),bot_lt_iff_ne_bot.2 <| Ne.symm hx2.2⟩
  rw [← hx3]
  constructor
  · use hx1, bot_lt_iff_ne_bot.2 <| Ne.symm hx2.2
  · apply sInf_le_sInf_of_forall_exists_le
    rintro y ⟨hy1,⟨hy2,hy3⟩⟩
    use μ ⟨(hy1,hx1) , lt_of_le_of_ne hy2.1.2 hy2.2⟩
    constructor
    · use hy1, hy2
    · exact hy3 ▸ (rmk4d10₀ μ ⟨(hy1,hx1), lt_of_le_of_ne hy2.1.2 hy2.2⟩).2


lemma prop4d18₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : semistable μ)
(h : (prop_4_1_cond₁ μ ∧ prop_4_1_cond₂ μ) ∨ (prop_4_3_cond₁ μ ∧ prop_4_3_cond₂ μ)) :
NashEquilibrium μ := by
  refine eq_of_le_of_le ?_ (prop4d18₁ μ hμ)
  cases' h with h h
  · exact impl.prop4d1₂ ℒ S μ h.1 h.2
  · exact impl.prop4d3₂ μ h.1 h.2


lemma prop4d20 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℒ, (hx : x ≠ ⊥) → prop_4_1_cond₁ (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ))
(h₂ :  ∀ x : ℒ, (hx : x ≠ ⊥) → prop_4_1_cond₂ (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ)) :
NashEquilibrium μ → semistable μ := by
  intro h
  have : sSup {μA μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ | (x : ℒ) (hx : x ≠ ⊥)} = μBstar μ := by
    unfold μBstar μB
    congr 1; ext
    constructor
    · simp
      intro x hx hx'
      rw [← hx']
      use x, ⟨in_TotIntvl _,Ne.symm hx⟩
      refine impl.stupid_helper ?_ (Eq.symm <| impl.prop4d1₁ (Interval ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩) S (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ μ) (h₁ x hx) (h₂ x hx)) ?_
      · simp [μmin]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ⟨ha1,ha2.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha2.2⟩
          rw [← ha3]
          congr 1
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ha1, ⟨in_TotIntvl ha1,Subtype.coe_ne_coe.2 ha2.2⟩
          rw [← ha3]
          congr 1
      · simp [μAstar,μA]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ha1, ⟨in_TotIntvl ha1,Subtype.coe_ne_coe.2 ha2.2⟩
          rw [← ha3]
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use ⟨hb1, ⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩
            rw [← hb3]
            congr 1
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩
            rw [← hb3]
            congr 1
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ⟨ha1,ha2.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha2.2⟩
          rw [← ha3]
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩
            rw [← hb3]
            simp [Resμ]
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use ⟨hb1,⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩
            rw [← hb3]
            congr 1
    · simp
      intro x hx hx'
      rw [← hx']
      use x, Ne.symm hx.2
      refine impl.stupid_helper ?_ (impl.prop4d1₁ (Interval ⟨(⊥,x),bot_lt_iff_ne_bot.2 <| Ne.symm hx.2⟩) S (Resμ ⟨(⊥,x),bot_lt_iff_ne_bot.2 <| Ne.symm hx.2⟩ μ) (h₁ x <| Ne.symm hx.2) (h₂ x <| Ne.symm hx.2)) ?_
      · simp [μAstar,μA,Resμ]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ⟨ha1,ha2.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha2.2⟩
          rw [← ha3]
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩
            rw [← hb3]
            simp [Resμ]
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use ⟨hb1,⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩
            rw [← hb3]
            congr 1
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ha1, ⟨in_TotIntvl ha1,Subtype.coe_ne_coe.2 ha2.2⟩
          rw [← ha3]
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use ⟨hb1, ⟨bot_le,hb2.1.2⟩⟩, ⟨hb2.1,Subtype.coe_ne_coe.1 hb2.2⟩
            rw [← hb3]
            congr 1
          · rintro ⟨hb1,⟨hb2,hb3⟩⟩
            use hb1, ⟨hb2.1,Subtype.coe_ne_coe.2 hb2.2⟩
            rw [← hb3]
            congr 1
      · simp [μmin]
        congr 1; ext
        constructor
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ha1, ⟨in_TotIntvl ha1,Subtype.coe_ne_coe.2 ha2.2⟩
          rw [← ha3]
          congr 1
        · rintro ⟨ha1,⟨ha2,ha3⟩⟩
          use ⟨ha1,ha2.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha2.2⟩
          rw [← ha3]
          congr 1
  have : ∀ x : ℒ, (hx : x ≠ ⊥) → μA μ ⟨(⊥,x),bot_lt_iff_ne_bot.2 hx⟩ ≤ μA μ TotIntvl := by
    rw [← h] at this
    simp [μAstar] at this
    intro x hx
    unfold TotIntvl
    rw [← this]
    apply le_sSup
    use x, hx
  exact fun x hx ↦ LE.le.not_lt <| this x hx


theorem thm4d21 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : SlopeLike μ)
(h₁ : prop_4_1_cond₁ μ) (h₂ : prop_4_3_cond₁ μ) :
List.TFAE [
  μmax μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μ TotIntvl,
  μmin μ TotIntvl = μmax μ TotIntvl,
  NashEquilibrium μ,
  semistable μ
  ] := by
  have h16 := prop4d16₁ μ hμ
  tfae_have 1 ↔ 2 := (h16.out 0 1 (by norm_num) (by norm_num))
  tfae_have 2 ↔ 3 := (h16.out 1 2 (by norm_num) (by norm_num))
  tfae_have 3 ↔ 4 := prop4d16₂ μ hμ h₁ h₂
  tfae_have 4 → 5 := by
    refine fun h ↦ prop4d20 μ ?_ ?_ h
    · intro x hx
      simp [prop_4_1_cond₁,Resμ]
      intro f smf
      rcases h₁ (fun t ↦ (f t).val) fun _ _ hxy ↦ lt_iff_le_not_le.2 (smf hxy) with ⟨N,hN⟩
      use N
      refine le_trans hN ?_

      sorry
    · intro x hx
      simp [prop_4_1_cond₂,Resμ]
      intro a b hab hb
      cases' (hμ a.val b.val x ⟨lt_iff_le_not_le.2 hab,lt_iff_le_not_le.2 hb⟩).1 with this this
      · exact Or.inl this
      · exact Or.inr <| le_of_lt this
  tfae_have 5 → 4 := by
    intro h
    refine prop4d18₂ μ h (Or.inl <| ⟨h₁,?_⟩)
    simp [prop_4_1_cond₂]
    intro a b hab hb
    cases' (hμ a b ⊤ ⟨hab,hb⟩).1 with this this
    · exact Or.inl this
    · exact Or.inr <| le_of_lt this
  tfae_finish

end impl
