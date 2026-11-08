import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native spinor representation owner

This module preserves the historical `SpinorRepNative` import path while
re-exporting the actual Clifford/spinor representation theorems from
`InfoGeometry.Clifford.SpinorRep`.  It contains no placeholder value or
prose-only evidence marker.
-/

namespace InfoGeometry.Clifford.SpinorRepNative

open InfoGeometry.Clifford.SpinorRep

/-- The split `Cl(1,1)` spinor representation is bijective onto `2 × 2` matrices. -/
theorem cl11_spinor_representation_bijective :
    Function.Bijective cl11ToMat :=
  cl11ToMat_bijective

/-- The Clifford generator squares to the split quadratic form in the spinor model. -/
theorem cl11_spinor_generator_square (v : ℝ × ℝ) :
    gamma₁₁ v * gamma₁₁ v = (q11 v) • (1 : Mat2) :=
  gamma₁₁_sq v

end InfoGeometry.Clifford.SpinorRepNative
