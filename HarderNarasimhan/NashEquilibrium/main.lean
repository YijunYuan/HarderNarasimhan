import HarderNarasimhan.Basic
import HarderNarasimhan.FirstMoverAdvantage.Impl
import HarderNarasimhan.SlopeLike.Defs
import Mathlib.Tactic.TFAE
import Mathlib.Data.List.TFAE

def NashEquilibrium {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
  μAstar ℒ S μ = μBstar ℒ S μ


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
μBstar ℒ S μ ≤ μAstar ℒ S μ ↔ ∀ x : ℒ, (hx : x ≠ ⊤) → ∀ y : ℒ, (hy : ⊥ < y) → μmin μ ⟨(⊥,y),hy⟩ ≤ μmax μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx⟩ := by
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
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩):
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
(h₁ : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩):
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
μmin μ TotIntvl = μmax μ TotIntvl → μBstar ℒ S μ ≤ μAstar ℒ S μ := by
  have h₁ : μBstar ℒ S μ ≤ μmax μ TotIntvl := by
    unfold μBstar μB μmax TotIntvl
    apply sSup_le
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    refine hb3 ▸ le_trans (rmk4d10₀ μ ⟨(⊥,hb1), bot_lt_iff_ne_bot.2 <| Ne.symm hb2.2⟩).1 <| le_sSup ?_
    use hb1, ⟨in_TotIntvl hb1, hb2.2⟩
  have h₂ : μmin μ TotIntvl ≤ μAstar ℒ S μ := by
    unfold μAstar μA μmin TotIntvl
    apply le_sInf
    rintro b ⟨hb1,⟨hb2,hb3⟩⟩
    refine hb3 ▸ le_trans (sInf_le ?_) (rmk4d10₀ μ ⟨(hb1,⊤), lt_top_iff_ne_top.2 <| hb2.2⟩).2
    use hb1, ⟨in_TotIntvl hb1, hb2.2⟩
  exact fun h ↦ le_trans h₁ (h ▸ h₂)


lemma prop4d11₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩)
(h₁' : ∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩)
(h₂' : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩):
μBstar ℒ S μ ≤ μAstar ℒ S μ → μmin μ TotIntvl = μmax μ TotIntvl := fun h ↦ eq_of_le_of_le (le_trans (rmk4d10₀ μ TotIntvl).1 (rmk4d10₀ μ ⟨(⊥,⊤),bot_lt_top⟩).2) <| (impl.prop4d3₁ μ h₁' h₂') ▸ (impl.prop4d1₁ ℒ S μ h₁ h₂) ▸ h


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
