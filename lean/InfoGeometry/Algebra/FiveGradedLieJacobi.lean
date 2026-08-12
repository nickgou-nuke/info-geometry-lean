import InfoGeometry.Algebra.FiveGradedLieAntisymmetry

/-!
# Jacobi identity for a five-graded Lie carrier

The five distinguished components live inside an ambient mathlib Lie algebra.
Consequently Jacobi is inherited from `LieRing`; this owner does not yet claim
that any nested bracket belongs to a particular graded component.
-/

namespace InfoGeometry.Algebra.FiveGradedLieAntisymmetry

open InfoGeometry.Algebra.FiveGradedTKK

variable (R L : Type*) [CommRing R]
variable [LieRing L] [LieAlgebra R L]

namespace FiveGradedLieCarrier

variable (G : FiveGradedLieCarrier R L)

/-- Homogeneous inputs satisfy the ambient cyclic Jacobi identity. Grade
membership records the intended five-graded inputs without asserting bracket
closure, which remains a separate theorem debt. -/
theorem lie_jacobi_identity
    {u v w : Weight5} {x y z : L}
    (_hx : G.IsHomogeneous (R := R) (L := L) u x)
    (_hy : G.IsHomogeneous (R := R) (L := L) v y)
    (_hz : G.IsHomogeneous (R := R) (L := L) w z) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  exact lie_jacobi x y z

end FiveGradedLieCarrier

end InfoGeometry.Algebra.FiveGradedLieAntisymmetry
