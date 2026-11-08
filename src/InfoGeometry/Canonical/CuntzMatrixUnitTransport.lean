import Mathlib.Data.Matrix.Basis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge

/-!
# Finite matrix-unit transport

This is the unconditional finite generator layer available from the existing
`CuntzTwoIsometry` data.  It does not pretend to construct the missing
all-stage boundary representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge

open Matrix

theorem matrixToCuntz_stdBasisMatrix {K A : Type*} [CommRing K] [Ring A]
    [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (i j : Fin 2) :
    matrixToCuntz ck (Matrix.single i j 1) =
      (if i = 0 then ck.S1 else ck.S2) *
        star (if j = 0 then ck.S1 else ck.S2) := by
  fin_cases i <;> fin_cases j <;>
    simp [matrixToCuntz, Matrix.single]

end InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge
