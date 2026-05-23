import InfoGeometry.Algebra.Zorn.NullCone
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.Incidence

Representative-level incidence for the bundled Zorn null cone.

This file introduces the polar form of the reduced Zorn determinant and the
resulting incidence predicate on null representatives. It stays local to the
algebraic boundary and does not quotient the incidence relation yet.
-/

namespace InfoGeometry.Algebra.Zorn

variable {R : Type*} [CommRing R]

/--
Polar form associated to the reduced Zorn determinant.

This is the quadratic polarization
`detZ (X + Y) - detZ X - detZ Y`.
-/
def polarZ (X Y : ZornMatrix R) : R :=
  detZ (X + Y) - detZ X - detZ Y

@[simp] theorem polarZ_symm (X Y : ZornMatrix R) :
    polarZ X Y = polarZ Y X := by
  unfold polarZ
  rw [add_comm Y X]
  ring_nf

/--
Incidence between two bundled Zorn representatives.

This is the local polar-orthogonality predicate.
-/
def IncidentRep (X Y : ZornMatrix R) : Prop :=
  polarZ X Y = 0

@[simp] theorem IncidentRep.symm (X Y : ZornMatrix R) :
    IncidentRep X Y ↔ IncidentRep Y X := by
  unfold IncidentRep
  rw [polarZ_symm]

end InfoGeometry.Algebra.Zorn
