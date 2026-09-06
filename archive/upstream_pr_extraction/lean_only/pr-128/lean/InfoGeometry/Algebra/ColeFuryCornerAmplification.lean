import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Amplification of the associative quadrant

The associative quadrant is `M₂(ℤ)`.  Its spinor-block readout is the
Kronecker amplification `A ↦ A ⊗ₖ I₁₆`; no entrywise `32 × 32` calculation is
needed for its multiplicativity.
-/

namespace InfoGeometry.Algebra.ColeFury

abbrev CornerMatrix := Matrix (Fin 2) (Fin 2) ℤ
abbrev AmplifiedMatrix := Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℤ

def amplify (A : CornerMatrix) : AmplifiedMatrix :=
  Matrix.kronecker A (1 : Matrix (Fin 16) (Fin 16) ℤ)

theorem amplify_mul (A B : CornerMatrix) :
    amplify (A * B) = amplify A * amplify B := by
  simpa [amplify] using
    (Matrix.mul_kronecker_mul A B
      (1 : Matrix (Fin 16) (Fin 16) ℤ)
      (1 : Matrix (Fin 16) (Fin 16) ℤ))

end InfoGeometry.Algebra.ColeFury
