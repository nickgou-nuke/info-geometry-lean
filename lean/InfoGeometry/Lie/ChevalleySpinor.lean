import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Split quadratic forms

This owner records only the orthogonal-difference quadratic form.  Clifford
even-subalgebra maps, spinor actions, cyclic traces, and matrix divergences
belong to their native Mathlib or domain-specific owners.
-/

namespace InfoGeometry.Lie.ChevalleySpinor

/-! ## Split quadratic forms -/

/-- Orthogonal difference of two quadratic forms on a product module. -/
def splitQuadraticForm {R : Type*} [CommRing R]
    {Mp Mm : Type*} [AddCommGroup Mp] [AddCommGroup Mm]
    [Module R Mp] [Module R Mm]
    (Qp : QuadraticForm R Mp) (Qm : QuadraticForm R Mm) :
    QuadraticForm R (Mp × Mm) :=
  Qp.comp (LinearMap.fst R Mp Mm) + (-Qm).comp (LinearMap.snd R Mp Mm)

end InfoGeometry.Lie.ChevalleySpinor
