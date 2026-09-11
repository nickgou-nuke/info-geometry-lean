import InfoGeometry.Clifford.Cl55WittReflectionDeterminant
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Orientation of a pair of split-quadratic reflections

This is a finite determinant readout only.  It proves that the product of two
anisotropic reflections has determinant `+1`; it is not an identification of
the native Spin image with the full special orthogonal group.
-/

theorem quadraticReflectionElement_pair_det
    (v w : V55)
    (hv : Q55 v ≠ 0)
    (hw : Q55 w ≠ 0) :
    (quadraticReflectionElement v hv *
        quadraticReflectionElement w hw).1.det = (1 : ℝˣ) := by
  change LinearEquiv.det
      ((quadraticReflectionElement v hv).1 *
        (quadraticReflectionElement w hw).1) = 1
  rw [map_mul, quadraticReflectionElement_det v hv,
    quadraticReflectionElement_det w hw]
  simp

end InfoGeometry.Clifford.Clifford55
