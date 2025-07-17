import HarderNarasimhan.Basic

def NashEquilibrium {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop :=
  μAstar μ = μBstar μ
