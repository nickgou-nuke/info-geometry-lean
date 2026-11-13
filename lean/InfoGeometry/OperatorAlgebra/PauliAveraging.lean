/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJones
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Four-term averaging in the existing two-sheet matrix algebra

The clock, exchange, and skew-exchange matrices are the existing
`Gamma_mat`, `J_mat`, and `K_mat` owners. Their four conjugations give an
unnormalized average in the full matrix algebra over any star ring. The output
has equal diagonal entries; those entries need not be central in the coefficient
ring. No division, characteristic-zero assumption, or cyclic trace is used.

The corner identities are finite algebra. They specify neither a metric porous
set nor a Cantor construction, and imply no strict operator-norm contraction.
-/

namespace InfoGeometry.OperatorAlgebra.PauliAveraging

open InfoGeometry.Clifford

variable {B : Type*} [Ring B] [StarRing B]

/-- The unnormalized sum of the identity and three existing sheet conjugations. -/
def pauliSum (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  M + Gamma_mat * M * star Gamma_mat + J_mat * M * star J_mat +
    K_mat * M * star K_mat

/-- Four conjugations cancel the off-diagonal entries. This is valid even with
noncommuting coefficient entries and in characteristic two. -/
theorem pauliSum_eq_scalar (M : Matrix (Fin 2) (Fin 2) B) :
    pauliSum M = Matrix.scalar (Fin 2) (2 * (M 0 0 + M 1 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliSum, Gamma_mat, J_mat, K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.star_apply, Matrix.scalar_apply, Fin.sum_univ_two] <;> noncomm_ring

/-- The unnormalized sum is scaled idempotent, with scale four. -/
theorem pauliSum_twice (M : Matrix (Fin 2) (Fin 2) B) :
    pauliSum (pauliSum M) = 4 • pauliSum M := by
  rw [pauliSum_eq_scalar, pauliSum_eq_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, nsmul_eq_mul] <;> noncomm_ring

/-- The four conjugates of the first coordinate projection sum to twice the unit. -/
theorem pauliSum_firstCorner :
    pauliSum (Matrix.single 0 0 (1 : B)) = 2 := by
  rw [pauliSum_eq_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.ofNat_apply]

/-- The first coordinate projection and its exchange conjugate partition the unit. -/
theorem firstCorner_add_exchange :
    Matrix.single 0 0 (1 : B) +
      J_mat * Matrix.single 0 0 (1 : B) * star J_mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.star_apply, Fin.sum_univ_two]

end InfoGeometry.OperatorAlgebra.PauliAveraging
