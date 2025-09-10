import HarderNarasimhan.Basic

namespace HarderNarasimhan

class NashEquilibrium {ℒ : Type*} [Nontrivial ℒ] [PartialOrder ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) : Prop where
  nash_eq : μAstar μ = μBstar μ

end HarderNarasimhan
