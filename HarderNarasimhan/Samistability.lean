import HarderNarasimhan.Convexity
def ACCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop := ∀ f : ℕ → ℒ, (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≤ f (n + 1)) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def ACCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] : Prop := ACCondI ℒ (⊥ , ⊤) bot_lt_top

def μDCCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (InInterval I a) → (∀ n : ℕ, InInterval I (f n)) → (∀ n : ℕ, f n ≥ f (n + 1)) → (∀ n : ℕ, f n > a) → (∀ n : ℕ, μA μ (a, f n) < μA μ (a, f (n+1))) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def μDCCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] {S : Type} [CompleteLattice S] (μ : ℒ × ℒ → S) : Prop :=
  μDCCondI ℒ μ (⊥ , ⊤) bot_lt_top

lemma clearly (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (h : μDCCond ℒ μ) (x : ℒ) (hx : x ≠ ⊤) : μDCCondI ℒ μ (x , ⊤) (lt_top_iff_ne_top.2 hx) := sorry

lemma prop3d2 (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) (h : μDCCond ℒ μ) (x : ℒ) (z : ℒ) (h : I.1 ≤ x ∧ x < z ∧ z ≤ I.2) (h' : μA μ (x , z) = ⊤) (a : ℒ) (ha : I.1 < a ∧ a < x) : μA μ (a , x) < μA μ (a , z)  := sorry
