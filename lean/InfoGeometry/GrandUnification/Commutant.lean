import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Basic

/-!
# Algebraic commutants of operator sets

The commutant of a set of endomorphisms consists of the endomorphisms that
commute with every member of that set.  This is the shared algebraic owner used
by the modular-conjugation developments.
-/

namespace InfoGeometry.GrandUnification

variable {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M]

/-- The commutant of a set of module endomorphisms. -/
def Commutant (A : Set (Module.End R M)) : Set (Module.End R M) :=
  {y | ∀ x ∈ A, x * y = y * x}

/-- Membership in a commutant is exactly pointwise commutation with its set. -/
theorem mem_commutant_iff (A : Set (Module.End R M)) (y : Module.End R M) :
    y ∈ Commutant A ↔ ∀ x ∈ A, x * y = y * x := Iff.rfl

end InfoGeometry.GrandUnification
