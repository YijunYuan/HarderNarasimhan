import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Interval

def μDCC {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → (h₂ : ∀ n : ℕ, f n > f (n + 1)) →  ∃ N : ℕ, μA μ ⟨(a, f <| N + 1), h₁ <| N + 1⟩ ≤ μA μ ⟨(a, f N), h₁ N⟩


def S₁I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ > μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩


def S₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x)  (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ = μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.1 hx⟩ → y ≤ x


def StI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Set ℒ :=
{l : ℒ | ∃ hlI : InIntvl I l , ∃ hl : I.val.1 ≠ l ,  (S₁I μ I l hlI hl) ∧ (S₂I μ I l hlI hl)}


def St {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Set ℒ :=
StI μ TotIntvl


def semistableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := I.val.2 ∈ StI μ I


def semistable {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop := semistableI μ TotIntvl


theorem semistableI_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : semistableI μ I ↔ semistable (↑μ : {p : (Interval I) × (Interval I) // p.1 < p.2} → S) := by
  constructor
  · intro h
    simp [semistable,semistableI]
    simp [semistableI] at h
    rcases h.out with ⟨h1,h2,h3,h4⟩
    apply Set.mem_def.2
    refine Set.setOf_app_iff.mpr ?_
    use in_TotIntvl (TotIntvl.val).2
    use ne_of_lt (TotIntvl.prop)
    constructor
    · simp [S₁I] at *
      intro y hyI hy
      have := h3 y hyI (Subtype.coe_ne_coe.2 hy)
      by_contra fuck
      refine this ?_
      refine lt_of_eq_of_lt ?_ (lt_of_lt_of_eq fuck ?_)
      · simp [μA]
        congr 1
        ext
        simp only [Set.mem_setOf_eq, Subtype.coe_mk]
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,ha1.1⟩, ⟨in_TotIntvl _,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          simp only [Set.mem_setOf_eq, Subtype.coe_mk]
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
          · simp [μmax]
            congr 1; ext
            constructor
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use ⟨c,⟨le_trans b.prop.1 hc1.1.1,hc1.1.2⟩⟩, ⟨hc1.1,Subtype.coe_ne_coe.1 hc1.2⟩
            · rintro ⟨c,⟨hc1,hc2⟩⟩
              rw [← hc2]
              use c.val, ⟨hc1.1,Subtype.coe_ne_coe.2 hc1.2⟩
      · simp [μA]
        congr 1; ext
        constructor
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use a.val, ⟨ha1.1,Subtype.coe_ne_coe.2 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            simp
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
        · rintro ⟨a,⟨ha1,ha2⟩⟩
          rw [← ha2]
          use ⟨a,⟨ha1.1.1,le_trans ha1.1.2 y.prop.2⟩⟩, ⟨ha1.1,Subtype.coe_ne_coe.1 ha1.2⟩
          simp [μmax]
          congr 1; ext
          constructor
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use b.val, ⟨hb1.1,Subtype.coe_ne_coe.2 hb1.2⟩
          · rintro ⟨b,⟨hb1,hb2⟩⟩
            rw [← hb2]
            use ⟨b,⟨le_trans ha1.1.1 hb1.1.1,le_trans hb1.1.2 y.prop.2⟩⟩, ⟨hb1.1,Subtype.coe_ne_coe.1 hb1.2⟩
    · sorry
  · sorry


def stableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
semistableI μ I ∧ ∀ x : ℒ, (hxI : InIntvl I x) → (hx : x ≠ I.val.1) → μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx.symm⟩ ≠ μA μ ⟨(I.val.1 , I.val.2) , I.prop⟩


def stable {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
stableI μ TotIntvl
