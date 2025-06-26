import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic

section

variable (R : Type) [CommRing R] [IsNoetherianRing R]
variable (M : Type) [Nontrivial M] [AddCommGroup M] [Module R M] [Module.Finite R M]

--abbrev ℒ : Type := Submodule R M
--notation ℒ := Submodule R M

variable (p : Submodule R M) (q : Submodule R M)
#check p ≤ q

instance : BoundedOrder (Submodule R M) := by
  exact { toOrderTop := Submodule.instOrderTop, toOrderBot := Submodule.instOrderBot }

end
