import InfoGeometry.Canonical.F4ActionMatrixRationalMinor
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Exact replay target for the rational F₄ action certificate.

The matrix is generated from the finite coordinate certificate.  This owner
keeps the arithmetic replay separate from the later native-readback theorem.
-/

namespace InfoGeometry.Canonical.F4ActionMatrix

open scoped Matrix

def f4ActionMinorDeterminant : ℚ :=
  Matrix.det f4ActionMinor

end InfoGeometry.Canonical.F4ActionMatrix
