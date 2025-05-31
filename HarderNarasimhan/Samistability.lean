import HarderNarasimhan.Convexity
def ACCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop := ∀ f : ℕ → ℒ, (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≤ f (n + 1)) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def ACCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] : Prop := ACCondI ℒ (⊥ , ⊤) bot_lt_top

def μDCCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (InInterval I a) → (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≥ f (n + 1)) → (∀ n : ℕ, f n > a) → (∀ n : ℕ, μA μ (a, f n) < μA μ (a, f (n+1))) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def μDCCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) : Prop :=
  μDCCondI ℒ μ (⊥ , ⊤) bot_lt_top

lemma clearly (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (h : μDCCond ℒ μ) (x : ℒ) (hx : x ≠ ⊤) : μDCCondI ℒ μ (x , ⊤) (lt_top_iff_ne_top.2 hx) := sorry

lemma prop3d2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (h : μDCCond ℒ μ) (x : ℒ) (z : ℒ) (h : I.1 ≤ x ∧ x < z ∧ z ≤ I.2) (h' : μA μ (x , z) = ⊤) (a : ℒ) (ha : I.1 < a ∧ a < x) : μA μ (a , x) ≤ μA μ (a , z)  := sorry

lemma cor3d3 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (hI : I.1 < I.2) (f : ℕ → ℒ) (hfI : ∀ n : ℕ, InInterval I (f n)) (hfm : ∀ n : ℕ, f n > f (n + 1)) (h : ∃ N : ℕ, μA μ (f (N + 1) , f N) = ⊤) : μDCCondI ℒ μ I hI := sorry



def S₁I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (x : ℒ) (_ : InInterval I x) : Prop := ∀ y : ℒ, InInterval I y → y ≠ I.1 → ¬ μA μ (I.1 , y) > μA μ (I.1 , x)

def S₂I {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (x : ℒ) (_ : InInterval I x) : Prop := ∀ y : ℒ, InInterval I y → y ≠ I.1 → μA μ (I.1 , y) = μA μ (I.1 , x) → y ≤ x

lemma prop3d4 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (hI : I.1 < I.2) (hACC : ACCondI ℒ I hI) (hμDCC : μDCCondI ℒ μ I hI) : ∃ x : ℒ, ∃ hxI : InInterval I x,  (x ≠ I.1) ∧ (S₁I μ I hI x hxI) ∧ (S₂I μ I hI x hxI) := sorry

lemma rmk3d5 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] [LinearOrder S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (hI : I.1 < I.2) (x : ℒ) (hxI : InInterval I x) (hxS₁ : S₁I μ I hI x hxI) (hxS₂ : S₂I μ I hI x hxI) (y : ℒ) (hyI : InInterval I y) (hyS₁ : S₁I μ I hI y hyI) (hyS₂ : S₂I μ I hI y hyI) : x = y := sorry

def semistable {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (hI : I.1 < I.2) : Prop :=  S₁I μ I hI I.2 ⟨le_of_lt hI, le_rfl⟩ ∧ S₂I μ I hI I.2 ⟨le_of_lt hI, le_rfl⟩
