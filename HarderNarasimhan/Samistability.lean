import HarderNarasimhan.Convexity
def ACCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (I : {p : ℒ × ℒ // p.1 < p.2}) : Prop := ∀ f : ℕ → ℒ, (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≤ f (n + 1)) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def ACCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] : Prop := ACCondI ℒ ⟨(⊥ , ⊤) , bot_lt_top⟩

def μDCCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (InInterval I a) → (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≥ f (n + 1)) → (hlta : ∀ n : ℕ, f n > a) → (∀ n : ℕ, μA μ ⟨(a, f n) , hlta n⟩ < μA μ ⟨(a, f (n+1)) , hlta (n + 1)⟩) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def μDCCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) : Prop :=
  μDCCondI ℒ μ ⟨(⊥ , ⊤) , bot_lt_top⟩

lemma clearly (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (h : μDCCond ℒ μ) (x : ℒ) (hx : x ≠ ⊤) : μDCCondI ℒ μ ⟨(x , ⊤) , lt_top_iff_ne_top.2 hx⟩ := sorry

lemma prop3d2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
--(h : μDCCond ℒ μ)
(x : ℒ) (hxI : InInterval I x)
(z : ℒ) (hzI : InInterval I z)
(h : x < z)
(h' : μA μ ⟨(x , z) , h⟩ = ⊤)
(a : ℒ) (haI : InInterval I a) (hax : a < x):
μA μ ⟨(a , x) , hax⟩ ≤ μA μ ⟨(a , z) , lt_trans hax h⟩ :=
sorry

lemma cor3d3 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(f : ℕ → ℒ)
(hfI : ∀ n : ℕ, InInterval I (f n))
(hfm : ∀ n : ℕ, f (n + 1) < f n)
(h : ∃ N : ℕ, μA μ ⟨(f (N + 1) , f N) , hfm N⟩ = ⊤) : μDCCondI ℒ μ I := sorry



def S₁I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InInterval I x) (hx : x ≠ I.val.1): Prop := ∀ y : ℒ, (hyI : InInterval I y) → (hy : y ≠ I.val.1) → ¬ μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left (hy.symm)⟩ > μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left (hx.symm)⟩ → y ≤ x

def S₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InInterval I x)  (hx : x ≠ I.val.1): Prop := ∀ y : ℒ, (hyI : InInterval I y) → (hy : y ≠ I.val.1) → μA μ ⟨(I.val.1 , y) , lt_of_le_of_ne hyI.left (hy.symm)⟩ = μA μ ⟨(I.val.1 , x) , lt_of_le_of_ne hxI.left (hx.symm)⟩ → y ≤ x

lemma prop3d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(hACC : ACCondI ℒ I)
(hμDCC : μDCCondI ℒ μ I) : ∃ x : ℒ, ∃ hxI : InInterval I x,  ∃ hx : x ≠ I.val.1, (S₁I μ I x hxI hx) ∧ (S₂I μ I x hxI hx) := sorry

lemma rmk3d5 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
(S : Type) [CompleteLattice S] [LinearOrder S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2})
(x : ℒ) (hxI : InInterval I x) (hx : x ≠ I.val.1)
(hxS₁ : S₁I μ I x hxI hx)
(hxS₂ : S₂I μ I x hxI hx)
(y : ℒ) (hyI : InInterval I y) (hy : y ≠ I.val.1)
(hyS₁ : S₁I μ I y hyI hy)
(hyS₂ : S₂I μ I y hyI hy) : x = y := sorry

def semistable {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : ℒ × ℒ → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) : Prop :=  S₁I μ I I.val.2 ⟨le_of_lt I.prop, le_rfl⟩ (ne_of_lt I.prop).symm ∧ S₂I μ I I.val.2 ⟨le_of_lt I.prop, le_rfl⟩ (ne_of_lt I.prop).symm
