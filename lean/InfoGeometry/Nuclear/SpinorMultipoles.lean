import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.CyclotomicSplitting.AlgebraicPolarization

noncomputable section

namespace InfoGeometry.Nuclear.SpinorMultipoles

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open scoped Kronecker

theorem square_zero_pow_vanishes {Carrier : Type*} [MonoidWithZero Carrier]
    (operator : Carrier) (square_zero : operator * operator = 0)
    (power : ℕ) (at_least_two : 2 ≤ power) : operator ^ power = 0 := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_add_of_le at_least_two
  rw [pow_add, pow_two, square_zero, zero_mul]

theorem pauli_raising_cube_zero : wittCreationBase ^ 3 = 0 := by
  exact square_zero_pow_vanishes wittCreationBase wittCreationBase_sq 3 (by decide)

def raisingTensor (factors : ℕ) : Mat factors :=
  kronPow wittCreationBase factors

def zeroIndex : (factors : ℕ) → Idx factors
  | 0 => 0
  | factors + 1 => (zeroIndex factors, 0)

def oneIndex : (factors : ℕ) → Idx factors
  | 0 => 0
  | factors + 1 => (oneIndex factors, 1)

theorem raisingTensor_corner (factors : ℕ) :
    raisingTensor factors (zeroIndex factors) (oneIndex factors) = 1 := by
  induction factors with
  | zero => simp [raisingTensor, kronPow, zeroIndex, oneIndex]
  | succ factors induction_hypothesis =>
      change raisingTensor factors (zeroIndex factors) (oneIndex factors) *
        wittCreationBase 0 1 = 1
      rw [induction_hypothesis]
      norm_num [wittCreationBase]

theorem raisingTensor_ne_zero (factors : ℕ) : raisingTensor factors ≠ 0 := by
  intro vanishes
  have corner := congrArg
    (fun operator : Mat factors => operator (zeroIndex factors) (oneIndex factors)) vanishes
  rw [raisingTensor_corner] at corner
  norm_num at corner

theorem raisingTensor_succ_square_zero (factors : ℕ) :
    raisingTensor (factors + 1) * raisingTensor (factors + 1) = 0 := by
  change (raisingTensor factors ⊗ₖ wittCreationBase) *
    (raisingTensor factors ⊗ₖ wittCreationBase) = 0
  rw [← Matrix.mul_kronecker_mul, wittCreationBase_sq, Matrix.kronecker_zero]

theorem ordinary_cube_vs_tensor_cube :
    wittCreationBase ^ 3 = 0 ∧ raisingTensor 3 ≠ 0 := by
  exact ⟨pauli_raising_cube_zero, raisingTensor_ne_zero 3⟩

theorem raisingTensor_succ_not_periodic (factors order : ℕ)
    (at_least_two : 2 ≤ order) : raisingTensor (factors + 1) ^ order ≠ 1 := by
  rw [square_zero_pow_vanishes _ (raisingTensor_succ_square_zero factors)
    order at_least_two]
  exact zero_ne_one

theorem triangular_root_sum {Scalar : Type*} [Ring Scalar] [NoZeroDivisors Scalar]
    (root : Scalar) (periodic : root ^ 3 = 1) (nontrivial : root ≠ 1) :
    1 + root + root ^ 2 = 0 := by
  simpa only [add_comm, add_left_comm, add_assoc] using
    InfoGeometry.CyclotomicSplitting.triangular_root_identity root periodic nontrivial

theorem real_triangular_root_impossible (root : ℝ) : root ^ 2 + root + 1 ≠ 0 := by
  intro vanishes
  nlinarith [sq_nonneg (root + 1 / 2)]

end InfoGeometry.Nuclear.SpinorMultipoles
