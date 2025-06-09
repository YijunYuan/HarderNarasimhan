import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Convexity.Impl


def μDCC {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (h₁ : ∀ n : ℕ, f n > a) → (h₂ : ∀ n : ℕ, f n > f (n + 1)) →  ∃ N : ℕ, μA μ ⟨(a, f <| N + 1), h₁ <| N + 1⟩ ≤ μA μ ⟨(a, f N), h₁ N⟩


lemma prop3d2 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(I : {p : ℒ × ℒ // p.1 < p.2})
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvexI I μ)
(x : ℒ) (hxI : InIntvl I x)
(z : ℒ) (hzI : InIntvl I z)
(h : x < z)
(h' : μA μ ⟨(x , z) , h⟩ = ⊤)
(a : ℒ) (haI : InIntvl I a) (hax : a < x):
μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩ := by
  have h'' : μA μ ⟨(a , x) , hax⟩ ⊓ μA μ ⟨(x , z) , h⟩ ≤ μA μ ⟨(a,z),lt_trans hax h⟩ :=  by exact impl.prop2d6₁I I μ hμcvx a haI x hxI z hzI ⟨hax,h⟩
  rw [h', inf_top_eq] at h''
  exact h''


lemma cor3d3 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμcvx : IsConvex μ)
(h : ∀ f : ℕ → ℒ, (h : ∀ n : ℕ, f n > f (n + 1)) →  ∃N : ℕ, μA μ ⟨(f <| N + 1, f N),h N⟩ = ⊤)
: μDCC μ := by
  intro a f h₁ h₂
  rcases (h f h₂) with ⟨N, hN⟩
  use N
  exact prop3d2 TotIntvl μ hμcvx (f <| N + 1) (in_TotIntvl <| f <| N + 1) (f N) (in_TotIntvl <| f N) (h₂ N) hN a (in_TotIntvl <| a) (h₁ <| N + 1)


def S₁I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ > μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩ → y ≤ x


def S₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x)  (hx : I.val.1 ≠ x): Prop := ∀ y : ℒ, (hyI : InIntvl I y) → (hy : I.val.1 ≠ y) → μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left hy⟩ = μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx⟩ → y ≤ x


def St {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Set ℒ :=
{l : ℒ | ∃ hlI : InIntvl I l , ∃ hl : I.val.1 ≠ l ,  (S₁I μ I l hlI hl) ∧ (S₂I μ I l hlI hl)}


lemma prop3d4 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] -- The ascending chain condition. Actually we only need this condition on the Interval I, but to make the life easy, we require it on the whole ℒ.
-- This actually does `NOT` make the statement any weaker, since if we take I to be (⊥,⊤), then we can "apply" this global version to I itself, which is also a sublattice of ℒ.
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hμDCC : μDCC μ) : (St μ I).Nonempty := sorry


lemma rmk3d5 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S] [LinearOrder S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InIntvl I x) (hx : I.val.1 ≠ x)
(hxS₁ : S₁I μ I x hxI hx)
(hxS₂ : S₂I μ I x hxI hx)
(y : ℒ) (hyI : InIntvl I y) (hy : I.val.1 ≠ y)
(hyS₁ : S₁I μ I y hyI hy)
(hyS₂ : S₂I μ I y hyI hy) : x = y := sorry


def semistableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := I.val.2 ∈ St μ I


def stableI {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
semistableI μ I ∧ ∀ x : ℒ, (hxI : InIntvl I x) → (hx : x ≠ I.val.1) → μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left hx.symm⟩ ≠ μA μ ⟨(I.val.1 , I.val.2) , I.prop⟩


lemma prop3d7 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hx : x ≠ I.val.2)
(hxSt : x ∈ St μ I) :
semistableI μ ⟨(I.val.1 , x), lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ∧
∀ y : ℒ, (hyI : InIntvl I y) → (hy : y > x) → ¬ μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxSt.out.choose.1 hxSt.out.choose_spec.choose⟩ ≤ μA μ ⟨(x, y), hy⟩ := sorry


lemma prop3d8₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
IsTotal (St μ I) (· ≤ ·) := sorry


lemma prop3d8₁' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ]  [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩) :
∃ s : ℒ, IsGreatest (St μ I) s := by
expose_names
rcases inst_3.wf.has_min (St μ I) (prop3d4 μ I hμ) with ⟨M,hM⟩
use M
constructor
exact hM.1
refine mem_upperBounds.2 ?_
intro x hx
cases' (prop3d8₁ μ hμ I h).total ⟨x, hx⟩ ⟨M, hM.1⟩ with c1 c2
· exact c1
· simp at c2
  apply le_of_eq
  apply eq_of_ge_of_not_gt c2 (hM.2 x hx)


lemma prop3d8₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ)
(I : {p : ℒ × ℒ // p.1 < p.2})
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ z : ℒ, (hzI : InIntvl I z) → (hz : I.val.1 ≠ z) → ∃ u : S, u = μA μ ⟨(I.val.1 , z) , lt_of_le_of_ne hzI.left hz⟩)
(x : ℒ) (hxSt : x ∈ St μ I)
(y : ℒ) (hyI : InIntvl I y)
(hxy : x < y) :
μA μ ⟨(I.val.1 , y), lt_of_le_of_lt hxSt.out.choose.1 hxy⟩ = μA μ ⟨(x , y), hxy⟩ := sorry
