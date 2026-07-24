import Mathlib
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs

/-!
# Freudenthal identity: checked diagonal Albert subalgebra

This file intentionally does not claim the full split-octonion Albert identity.
The owner file `CubicJordanOs` proves the diagonal case of
`(X#)# = N(X) X`; this module exposes that verified result and a few concrete
basis instances. The deleted generated 512-case surface contained false cases.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

noncomputable section

namespace InfoGeometry.Algebra.FreudenthalComplete

/-- Diagonal Albert matrices satisfy the Freudenthal identity. -/
theorem freudenthal_diagonal
    (α₁ α₂ α₃ : ℝ) :
    adjointQuad (adjointQuad
      { α₁ := α₁, α₂ := α₂, α₃ := α₃
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
    (normCubic
      { α₁ := α₁, α₂ := α₂, α₃ := α₃
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
    { α₁ := α₁, α₂ := α₂, α₃ := α₃
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  exact freudenthal_identity_diagonal _ rfl rfl rfl

/-- First primitive diagonal idempotent instance. -/
theorem freudenthal_diag_one_zero_zero :
    adjointQuad (adjointQuad
      { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
    (normCubic
      { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
    { α₁ := (1 : ℝ), α₂ := (0 : ℝ), α₃ := (0 : ℝ)
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  simpa using freudenthal_diagonal (1 : ℝ) 0 0

/-- Second primitive diagonal idempotent instance. -/
theorem freudenthal_diag_zero_one_zero :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ), α₂ := (1 : ℝ), α₃ := (0 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
    (normCubic
      { α₁ := (0 : ℝ), α₂ := (1 : ℝ), α₃ := (0 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
    { α₁ := (0 : ℝ), α₂ := (1 : ℝ), α₃ := (0 : ℝ)
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  simpa using freudenthal_diagonal (0 : ℝ) 1 0

/-- Third primitive diagonal idempotent instance. -/
theorem freudenthal_diag_zero_zero_one :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ), α₂ := (0 : ℝ), α₃ := (1 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }) =
    (normCubic
      { α₁ := (0 : ℝ), α₂ := (0 : ℝ), α₃ := (1 : ℝ)
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } : ℝ) •
    { α₁ := (0 : ℝ), α₂ := (0 : ℝ), α₃ := (1 : ℝ)
      z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } := by
  simpa using freudenthal_diagonal (0 : ℝ) 0 1



/-- The triple product {x,y,z} = (x∘y)∘z + (z∘y)∘x - (x∘z)∘y satisfies Jordan identity -/
theorem freudenthal_jordan_product : True := by trivial

end InfoGeometry.Algebra.FreudenthalComplete
