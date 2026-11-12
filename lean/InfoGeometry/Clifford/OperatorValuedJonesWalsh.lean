/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.Algebra.IdempotentProjector
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Matrix.Basis

/-!
# Operator-valued Jones coordinates and Peirce extraction

The existing Jones generators give a linear synthesis map in the order
`(I_mat, Gamma_mat, J_mat, K_mat)`. Over every ring, raw extraction and
synthesis compose to doubling in both directions. Inverting `2` gives a
linear equivalence over the possibly noncommutative coefficient ring.

The Peirce lift is the native scalar-matrix embedding of the upper-left
entry. Its fourth coefficient for the convention `Ω = -K_mat` is the
negative of the fourth Jones coordinate. The final integral counterexample
records why the unconditional doubled identity is not an integral basis
theorem. Internal twists reuse these generators and expose their exact
coefficient-commutation condition. No tensor-product or analytic transform
identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.OperatorValuedJonesWalsh

variable {B : Type*} [Ring B]

/-- Synthesis in the existing Jones order `(I, Γ, J, K)`. -/
def synthesis : (Fin 4 → B) →ₗ[B] Matrix (Fin 2) (Fin 2) B where
  toFun c := reconstruct_jones (c 0) (c 1) (c 2) (c 3)
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jones_decomposition_eq] <;> abel
  map_smul' b c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jones_decomposition_eq, mul_add, mul_sub]

@[simp] theorem synthesis_apply (c : Fin 4 → B) :
    synthesis c = !![c 0 + c 1, c 2 + c 3; c 2 - c 3, c 0 - c 1] :=
  jones_decomposition_eq (c 0) (c 1) (c 2) (c 3)

/-- Raw Jones extraction, requiring no division or characteristic assumption. -/
def rawCoordinates : Matrix (Fin 2) (Fin 2) B →ₗ[B] (Fin 4 → B) where
  toFun M := ![M 0 0 + M 1 1, M 0 0 - M 1 1,
    M 0 1 + M 1 0, M 0 1 - M 1 0]
  map_add' M N := by
    ext i
    fin_cases i <;> simp <;> abel
  map_smul' b M := by
    ext i
    fin_cases i <;> simp [mul_add, mul_sub]

/-- Raw extraction followed by synthesis recovers twice the matrix. -/
theorem synthesis_rawCoordinates (M : Matrix (Fin 2) (Fin 2) B) :
    synthesis (rawCoordinates M) = M + M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [synthesis, rawCoordinates, jones_decomposition_eq]

/-- Synthesis followed by raw extraction recovers twice each coefficient. -/
theorem rawCoordinates_synthesis (c : Fin 4 → B) :
    rawCoordinates (synthesis c) = c + c := by
  ext i
  fin_cases i <;>
    simp [synthesis, rawCoordinates, jones_decomposition_eq]

/-- Uniqueness of Jones synthesis requires only cancellation of doubling. -/
theorem synthesis_injective
    (hdouble : Function.Injective (fun b : B => b + b)) :
    Function.Injective (synthesis (B := B)) := by
  intro c d h
  have h' := congrArg (rawCoordinates (B := B)) h
  rw [rawCoordinates_synthesis, rawCoordinates_synthesis] at h'
  funext i
  exact hdouble (congrFun h' i)

/-- Raw extraction is faithful when doubling is cancellable. -/
theorem rawCoordinates_injective
    (hdouble : Function.Injective (fun b : B => b + b)) :
    Function.Injective (rawCoordinates (B := B)) := by
  intro M N h
  have h' := congrArg (synthesis (B := B)) h
  rw [synthesis_rawCoordinates, synthesis_rawCoordinates] at h'
  ext i j
  exact hdouble (congrFun (congrFun h' i) j)

section InvertibleTwo

variable [Invertible (2 : B)]

/-- Right multiplication by the inverse of `2` preserves left `B`-linearity. -/
def normalizedCoordinates : Matrix (Fin 2) (Fin 2) B →ₗ[B] (Fin 4 → B) where
  toFun M i := rawCoordinates M i * ⅟ (2 : B)
  map_add' M N := by
    ext i
    simp [add_mul]
  map_smul' b M := by
    ext i
    simp [mul_assoc]

private theorem doubling_injective_of_invertible_two :
    Function.Injective (fun b : B => b + b) := by
  intro x y h
  have h' := congrArg (fun b : B => b * ⅟ (2 : B)) h
  simpa only [← mul_two, mul_assoc, mul_invOf_self, mul_one] using h'

@[simp] theorem normalizedCoordinates_synthesis (c : Fin 4 → B) :
    normalizedCoordinates (synthesis c) = c := by
  ext i
  change rawCoordinates (synthesis c) i * ⅟ (2 : B) = c i
  rw [rawCoordinates_synthesis]
  change (c i + c i) * ⅟ (2 : B) = c i
  rw [← mul_two, mul_assoc, mul_invOf_self, mul_one]

@[simp] theorem synthesis_normalizedCoordinates
    (M : Matrix (Fin 2) (Fin 2) B) :
    synthesis (normalizedCoordinates M) = M := by
  apply rawCoordinates_injective doubling_injective_of_invertible_two
  rw [rawCoordinates_synthesis]
  ext i
  change rawCoordinates M i * ⅟ (2 : B) +
    rawCoordinates M i * ⅟ (2 : B) = rawCoordinates M i
  rw [← mul_two, mul_assoc, invOf_mul_self, mul_one]

/-- The four Jones coefficients are native left-module coordinates when `2`
is invertible. No commutativity of the coefficient ring is required. -/
def jonesLinearEquiv : (Fin 4 → B) ≃ₗ[B] Matrix (Fin 2) (Fin 2) B where
  toLinearMap := synthesis
  invFun := normalizedCoordinates
  left_inv := normalizedCoordinates_synthesis
  right_inv := synthesis_normalizedCoordinates

end InvertibleTwo

/-! ## The Peirce lift and the sign of the symplectic generator -/

/-- Extract the upper-left Peirce corner and copy it with the existing exchange
generator. The projector is Mathlib's native matrix unit. -/
def peirceFiberLift (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix (Fin 2) (Fin 2) B :=
  peirce11 (Matrix.single 0 0 1) M +
    J_mat * peirce11 (Matrix.single 0 0 1) M * J_mat

/-- The coordinate-free corner expression is the scalar-matrix embedding. -/
theorem peirceFiberLift_eq_scalar (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift M = Matrix.scalar (Fin 2) (M 0 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceFiberLift, peirce11, Matrix.single, J_mat,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.diagonal]

theorem peirceFiberLift_walsh_I (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift (M + J_mat * M * J_mat) =
      Matrix.scalar (Fin 2) (rawCoordinates M 0) := by
  rw [peirceFiberLift_eq_scalar]
  simp [rawCoordinates, J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem peirceFiberLift_walsh_Gamma (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift (M - J_mat * M * J_mat) =
      Matrix.scalar (Fin 2) (rawCoordinates M 1) := by
  rw [peirceFiberLift_eq_scalar]
  simp [rawCoordinates, J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem peirceFiberLift_walsh_J (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift (M * J_mat + J_mat * M) =
      Matrix.scalar (Fin 2) (rawCoordinates M 2) := by
  rw [peirceFiberLift_eq_scalar]
  simp [rawCoordinates, J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The `Ω = -K_mat` convention reverses the last extracted coefficient. -/
theorem peirceFiberLift_walsh_omega (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift (J_mat * M - M * J_mat) =
      Matrix.scalar (Fin 2) (-rawCoordinates M 3) := by
  rw [peirceFiberLift_eq_scalar]
  simp [rawCoordinates, J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, neg_sub]

/-- Pairing the four Peirce coefficients with `(I, Γ, J, Ω)` recovers twice
the matrix, including over rings where `2` is not invertible. -/
theorem peirce_walsh_reconstruction (M : Matrix (Fin 2) (Fin 2) B) :
    peirceFiberLift (M + J_mat * M * J_mat) * I_mat +
      peirceFiberLift (M - J_mat * M * J_mat) * Gamma_mat +
      peirceFiberLift (M * J_mat + J_mat * M) * J_mat +
      peirceFiberLift (J_mat * M - M * J_mat) * (-K_mat) = M + M := by
  rw [peirceFiberLift_walsh_I, peirceFiberLift_walsh_Gamma,
    peirceFiberLift_walsh_J, peirceFiberLift_walsh_omega]
  calc
    _ = synthesis (rawCoordinates M) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [synthesis, jones_decomposition_eq, I_mat, Gamma_mat, J_mat, K_mat,
          Matrix.mul_apply, Matrix.diagonal] <;> abel
    _ = M + M := synthesis_rawCoordinates M

/-! ## Internal square-sign twists and coefficient commutation -/

/-- Twisting the exchange generator by an internal square root of `-1`
changes its square from `1` to `-1`. -/
theorem internalExchange_sq (j : B) (hj : j * j = -1) :
    (j • (J_mat : Matrix (Fin 2) (Fin 2) B)) ^ 2 = -1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pow_two, J_mat, Matrix.mul_apply, Fin.sum_univ_two, hj]

/-- The intake's skew convention is `Ω = -K_mat`; its internal twist has
square `1` when `j * j = -1`. -/
theorem internalOmega_sq (j : B) (hj : j * j = -1) :
    (j • (-K_mat : Matrix (Fin 2) (Fin 2) B)) ^ 2 = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pow_two, K_mat, Matrix.mul_apply, Fin.sum_univ_two, hj]

/-- The internal exchange twist is odd for the existing grading. -/
theorem internalExchange_grading_anticomm (j : B) :
    (j • J_mat) * (Gamma_mat : Matrix (Fin 2) (Fin 2) B) +
      Gamma_mat * (j • J_mat) = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [J_mat, Gamma_mat]

/-- The internal skew twist is also odd for the existing grading. -/
theorem internalOmega_grading_anticomm (j : B) :
    (j • (-K_mat)) * (Gamma_mat : Matrix (Fin 2) (Fin 2) B) +
      Gamma_mat * (j • (-K_mat)) = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [K_mat, Gamma_mat]

/-- The two generators twisted by the same coefficient anticommute without
assuming that coefficient is central or that its square is `-1`. -/
theorem internalTwists_anticomm (j : B) :
    (j • J_mat) * (j • (-K_mat : Matrix (Fin 2) (Fin 2) B)) +
      (j • (-K_mat)) * (j • J_mat) = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [J_mat, K_mat]

/-- An internal twist commutes with a scalar fiber exactly when its internal
coefficient commutes with that fiber's coefficient. -/
theorem scalar_commute_internalExchange_iff (a j : B) :
    Commute (Matrix.scalar (Fin 2) a) (j • J_mat) ↔ Commute a j := by
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 1) h
    simpa [J_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal] using h01
  · intro h
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [J_mat, Matrix.mul_apply, Matrix.diagonal, h]

/-- The same exact commutation boundary holds for the twisted skew generator. -/
theorem scalar_commute_internalOmega_iff (a j : B) :
    Commute (Matrix.scalar (Fin 2) a) (j • (-K_mat)) ↔ Commute a j := by
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 1 0) h
    simpa [K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal] using h10
  · intro h
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [K_mat, Matrix.mul_apply, Matrix.diagonal, h]


/-! ## Integral boundary -/

/-- The integral Jones span omits the upper-left matrix unit: its two diagonal
entries would require a coefficient satisfying `2 * c = 1`. -/
theorem synthesis_int_not_surjective :
    ¬ Function.Surjective (synthesis (B := ℤ)) := by
  intro h
  obtain ⟨c, hc⟩ := h (!![1, 0; 0, 0])
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hc
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hc
  simp [synthesis, jones_decomposition_eq] at h00 h11
  omega

end InfoGeometry.Clifford.OperatorValuedJonesWalsh
