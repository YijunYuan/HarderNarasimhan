import HarderNarasimhan.Convexity
def ACCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop := ∀ f : ℕ → ℒ, (∀ n : ℕ, I.1 ≤ f n ∧ f n ≤ I.2) → (∀ n : ℕ, f n ≤ f (n + 1)) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def ACCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop := ACCondI ℒ (⊥ , ⊤) bot_lt_top

def μDCCondI (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (I.1 ≤ a ∧ a ≤ I.2) → (∀ n : ℕ, I.1 ≤ f n ∧ f n ≤ I.2) → (∀ n : ℕ, f n ≥ f (n + 1)) → (∀ n : ℕ, f n > a) → (∀ n : ℕ, μA μ (a, f n) < μA μ (a, f (n+1))) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def μDCCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) (I : ℒ × ℒ) (_ : I.1 < I.2) : Prop :=
  μDCCondI ℒ S μ (⊥ , ⊤) bot_lt_top
