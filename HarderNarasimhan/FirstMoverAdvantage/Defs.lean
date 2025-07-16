import HarderNarasimhan.FirstMoverAdvantage.Impl


def prop_4_1_cond₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩


def prop_4_1_cond₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩


def prop_4_3_cond₁ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ x : ℕ → ℒ, (saf : StrictAnti x) → ∃ N : ℕ, μ ⟨(⊥ , x N), lt_of_le_of_lt bot_le <| saf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x (N+1), x N), saf <| Nat.lt_add_one N⟩


def prop_4_3_cond₂ {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz : ⊥ < z.val.1) → μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ z ∨ μ ⟨(⊥,z.val.2),lt_trans hz z.prop⟩ ≤ μ ⟨(⊥,z.val.1),hz⟩
