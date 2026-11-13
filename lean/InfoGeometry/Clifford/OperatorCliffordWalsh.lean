/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Clifford.OperatorValuedJones
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Ordered Clifford coordinates over a noncommutative ring

The frame is the existing `(I_mat, Gamma_mat, J_mat, -K_mat)`.
Raw extraction and synthesis compose to doubling in both directions.
The exact multiplication rule keeps every coefficient in its input order.

When two is invertible in the coefficient ring, right normalization gives
a native equivalence of left modules over that same ring. No commuting
coefficient hypothesis, external complex scalar, or positivity is used.
-/

namespace InfoGeometry.Clifford.OperatorCliffordWalsh

variable {A : Type*} [Ring A]

/-- The four raw coordinates in the frame `(I, Gamma, J, -K)`. -/
def coefficients : Matrix (Fin 2) (Fin 2) A →+ (Fin 4 → A) where
  toFun M := ![M 0 0 + M 1 1, M 0 0 - M 1 1,
    M 0 1 + M 1 0, M 1 0 - M 0 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' M N := by ext i; fin_cases i <;> simp <;> abel

/-- Synthesis uses the previously constructed Jones frame, with its skew sign reversed. -/
def synthesis : (Fin 4 → A) →+ Matrix (Fin 2) (Fin 2) A where
  toFun c := reconstruct_jones (c 0) (c 1) (c 2) (-c 3)
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jones_decomposition_eq]
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jones_decomposition_eq] <;> abel

theorem synthesis_entries (c : Fin 4 → A) :
    synthesis c = !![c 0 + c 1, c 2 - c 3; c 2 + c 3, c 0 - c 1] := by
  change reconstruct_jones (c 0) (c 1) (c 2) (-c 3) = _
  simpa only [sub_eq_add_neg, neg_neg] using
    jones_decomposition_eq (c 0) (c 1) (c 2) (-c 3)

/-- Over an arbitrary ring the raw round trip is doubling. -/
theorem synthesis_coefficients (M : Matrix (Fin 2) (Fin 2) A) :
    synthesis (coefficients M) = M + M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis_entries, coefficients] <;> abel

/-- The reverse raw round trip is also doubling. -/
theorem coefficients_synthesis (c : Fin 4 → A) :
    coefficients (synthesis c) = c + c := by
  ext i
  fin_cases i <;> simp [coefficients, synthesis_entries]

/-- Synthesis respects right coefficient multiplication without a centrality assumption. -/
theorem synthesis_mul_right (c : Fin 4 → A) (a : A) :
    synthesis (fun i => c i * a) = (synthesis c).map (fun x => x * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis_entries, Matrix.map_apply, add_mul, sub_mul]

/-- The coefficient embeddings are native scalar matrices, not central coefficients. -/
theorem synthesis_scalar_frame (c : Fin 4 → A) :
    synthesis c =
      Matrix.scalar (Fin 2) (c 0) +
      Matrix.scalar (Fin 2) (c 1) * Gamma_mat +
      Matrix.scalar (Fin 2) (c 2) * J_mat +
      Matrix.scalar (Fin 2) (c 3) * (-K_mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis_entries, Matrix.scalar_apply, Matrix.diagonal,
      Matrix.mul_apply, Gamma_mat, J_mat, K_mat] <;> abel

/-- Duplicate the first Peirce corner into both diagonal fibers. -/
def peirceFiber (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.single 0 0 1 * M * Matrix.single 0 0 1 +
    J_mat * (Matrix.single 0 0 1 * M * Matrix.single 0 0 1) * J_mat

/-- The fiber construction is exactly the native scalar-matrix embedding of `M00`. -/
theorem peirceFiber_eq_scalar (M : Matrix (Fin 2) (Fin 2) A) :
    peirceFiber M = Matrix.scalar (Fin 2) (M 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [peirceFiber, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [J_mat, Matrix.scalar_apply, Matrix.diagonal]

theorem coefficient_zero_fiber (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.scalar (Fin 2) (coefficients M 0) = peirceFiber (M + J_mat * M * J_mat) := by
  rw [peirceFiber_eq_scalar]
  congr 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [coefficients, J_mat]

theorem coefficient_one_fiber (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.scalar (Fin 2) (coefficients M 1) = peirceFiber (M - J_mat * M * J_mat) := by
  rw [peirceFiber_eq_scalar]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [coefficients, J_mat]

theorem coefficient_two_fiber (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.scalar (Fin 2) (coefficients M 2) = peirceFiber (M * J_mat + J_mat * M) := by
  rw [peirceFiber_eq_scalar]
  congr 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [coefficients, J_mat]

theorem coefficient_three_fiber (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.scalar (Fin 2) (coefficients M 3) = peirceFiber (J_mat * M - M * J_mat) := by
  rw [peirceFiber_eq_scalar]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [coefficients, J_mat]

/-- Ordered multiplication of coefficients in the signed Clifford frame. -/
def convolution (c d : Fin 4 → A) : Fin 4 → A :=
  ![c 0 * d 0 + c 1 * d 1 + c 2 * d 2 - c 3 * d 3,
    c 0 * d 1 + c 1 * d 0 + c 2 * d 3 - c 3 * d 2,
    c 0 * d 2 + c 2 * d 0 - c 1 * d 3 + c 3 * d 1,
    c 0 * d 3 + c 3 * d 0 - c 1 * d 2 + c 2 * d 1]

/-- This is the product in the full matrix ring with arbitrary operator coefficients. -/
theorem synthesis_convolution (c d : Fin 4 → A) :
    synthesis (convolution c d) = synthesis c * synthesis d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis_entries, convolution, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- Raw coordinates multiply to twice the raw coordinates of the product. -/
theorem convolution_coefficients (M N : Matrix (Fin 2) (Fin 2) A) :
    convolution (coefficients M) (coefficients N) =
      coefficients (M * N) + coefficients (M * N) := by
  ext i
  fin_cases i <;>
    simp [convolution, coefficients, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- Two raw extractions followed by convolution synthesize four copies of the product. -/
theorem synthesis_convolution_coefficients (M N : Matrix (Fin 2) (Fin 2) A) :
    synthesis (convolution (coefficients M) (coefficients N)) =
      (M * N + M * N) + (M * N + M * N) := by
  rw [convolution_coefficients, map_add, synthesis_coefficients]

/-- Star reverses the skew coordinate and preserves the other three frame directions. -/
theorem coefficients_star [StarRing A] (M : Matrix (Fin 2) (Fin 2) A) :
    coefficients (star M) =
      ![star (coefficients M 0), star (coefficients M 1),
        star (coefficients M 2), -star (coefficients M 3)] := by
  ext i
  fin_cases i <;> simp [coefficients, star_add, star_sub]
  abel

section InvertibleTwo

variable [Invertible (2 : A)]

/-- Right normalization cancels doubling without commuting coefficient products. -/
theorem add_self_mul_invOf_two (a : A) : (a + a) * ⅟(2 : A) = a := by
  rw [← mul_two, mul_assoc, mul_invOf_self, mul_one]

/-- Divide the raw coordinates on the right, retaining left `A`-linearity. -/
def normalizedCoordinates (M : Matrix (Fin 2) (Fin 2) A) : Fin 4 → A :=
  fun i => coefficients M i * ⅟(2 : A)

theorem synthesis_normalizedCoordinates (M : Matrix (Fin 2) (Fin 2) A) :
    synthesis (normalizedCoordinates M) = M := by
  change synthesis (fun i => coefficients M i * ⅟(2 : A)) = M
  rw [synthesis_mul_right, synthesis_coefficients]
  ext i j
  exact add_self_mul_invOf_two (M i j)

theorem normalizedCoordinates_synthesis (c : Fin 4 → A) :
    normalizedCoordinates (synthesis c) = c := by
  ext i
  simp only [normalizedCoordinates, coefficients_synthesis, Pi.add_apply,
    add_self_mul_invOf_two]

/-- The full matrix module and its four coordinates are linearly equivalent when two is a unit. -/
def coordinateEquiv : Matrix (Fin 2) (Fin 2) A ≃ₗ[A] (Fin 4 → A) where
  toFun := normalizedCoordinates
  invFun := synthesis
  left_inv := synthesis_normalizedCoordinates
  right_inv := normalizedCoordinates_synthesis
  map_add' M N := by
    ext i
    simp only [normalizedCoordinates, map_add, Pi.add_apply, add_mul]
  map_smul' a M := by
    ext i
    fin_cases i <;>
      simp [normalizedCoordinates, coefficients] <;> noncomm_ring

theorem coordinateEquiv_apply (M : Matrix (Fin 2) (Fin 2) A) :
    coordinateEquiv M = normalizedCoordinates M := rfl

theorem coordinateEquiv_symm_apply (c : Fin 4 → A) :
    coordinateEquiv.symm c = synthesis c := rfl

/-- Normalized coordinates preserve the actual matrix multiplication via ordered convolution. -/
theorem normalizedCoordinates_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    normalizedCoordinates (M * N) =
      convolution (normalizedCoordinates M) (normalizedCoordinates N) := by
  apply coordinateEquiv.symm.injective
  change synthesis (normalizedCoordinates (M * N)) =
    synthesis (convolution (normalizedCoordinates M) (normalizedCoordinates N))
  rw [synthesis_convolution, synthesis_normalizedCoordinates,
    synthesis_normalizedCoordinates, synthesis_normalizedCoordinates]

end InvertibleTwo

end InfoGeometry.Clifford.OperatorCliffordWalsh
