import HarderNarasimhan.Convexity
def ACCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] : Prop := ∀ f : ℕ → ℒ, (∀ n : ℕ, f n ≤ f (n + 1)) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m

def μDCCond (ℒ : Type) [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] (S : Type) [CompleteLattice S] (μ : ℒ × ℒ → S) : Prop :=
  ∀ a : ℒ, ∀ f : ℕ → ℒ, (∀ n : ℕ, f n ≥ f (n + 1)) → (∀ n : ℕ, f n > a) → (∀ n : ℕ, μAI ℒ S μ (a, f n) < μAI ℒ S μ (a, f (n+1))) → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f n = f m
