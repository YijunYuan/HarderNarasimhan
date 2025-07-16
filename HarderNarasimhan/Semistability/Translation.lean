import HarderNarasimhan.Convexity.Defs
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.Interval
import HarderNarasimhan.Semistability.Impl

theorem semistable_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) :
------------
  semistable μ ↔ semistableI μ TotIntvl
------------
:= impl.semistable_iff μ

theorem semistableI_iff {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(I : {p : ℒ × ℒ // p.1 < p.2}) :
------------
semistableI μ I ↔ semistable (Resμ I μ)
------------
:= impl.semistableI_iff μ I
