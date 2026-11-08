import InfoGeometry.Algebra.Zorn.NullCone
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
def polarZ (cp : CrossProduct3 R) (X Y : ZornMatrix R) : R :=
  ZornMatrix.detZ cp (X + Y) - ZornMatrix.detZ cp X - ZornMatrix.detZ cp Y

@[simp] theorem polarZ_symm (cp : CrossProduct3 R) (X Y : ZornMatrix R) :
    polarZ cp X Y = polarZ cp Y X := by
  unfold polarZ
  rw [add_comm Y X]
  ring_nf

/--
Incidence between two bundled Zorn representatives.

This is the local polar-orthogonality predicate.
-/
def IncidentRep (cp : CrossProduct3 R) (X Y : ZornMatrix R) : Prop :=
  polarZ cp X Y = 0

@[simp] theorem IncidentRep.symm (cp : CrossProduct3 R) (X Y : ZornMatrix R) :
    IncidentRep cp X Y ↔ IncidentRep cp Y X := by
  unfold IncidentRep
  rw [polarZ_symm]

end InfoGeometry.Algebra.Zorn
