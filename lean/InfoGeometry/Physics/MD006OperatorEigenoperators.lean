import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.MD003IsomorphicRepresentations

/-!
# Repaired MD 006: finite operator algebra and eigenoperators

Source: `github-nick:nickgou-nuke/MD`, file `006.md`.

Chapter 6 develops left/right multiplication operators and the eigenoperator
basis of `M₂(ℂ)`.  This file formalizes the finite kernel-checkable core:

* left/right multiplication and their composition/commutation laws;
* left/right commutator laws as actions on a test matrix;
* explicit matrix units `E₁₁,E₁₂,E₂₁,E₂₂`;
* joint eigenoperator identities for left/right multiplication by `σ₃`;
* matrix-unit products, projectors, and nilpotents;
* Pauli decompositions of the matrix units;
* explicit complex-biquaternion coordinate representatives of the matrix units;
* `sl₂` root-vector commutators.

No abstract Lie-algebra isomorphism `gl₂ ⊕ gl₂`, Hilbert-space adjoint theorem,
representation-theoretic uniqueness theorem, or physical operator dynamics is
asserted beyond these finite identities.
-/

noncomputable section

namespace InfoGeometry.Physics.MD006OperatorEigenoperators

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry

/-- Left multiplication operator evaluated on a matrix. -/
def leftMul (A X : MatrixQuantumCarrier) : MatrixQuantumCarrier := A * X

/-- Right multiplication operator evaluated on a matrix. -/
def rightMul (A X : MatrixQuantumCarrier) : MatrixQuantumCarrier := X * A

/-- Matrix commutator. -/
def matrixComm (A B : MatrixQuantumCarrier) : MatrixQuantumCarrier := A * B - B * A

/-- Left multiplication operators compose in the same order. -/
theorem leftMul_comp (A B X : MatrixQuantumCarrier) :
    leftMul A (leftMul B X) = leftMul (A * B) X := by
  simp [leftMul, Matrix.mul_assoc]

/-- Right multiplication operators compose in the opposite matrix order. -/
theorem rightMul_comp (A B X : MatrixQuantumCarrier) :
    rightMul A (rightMul B X) = rightMul (B * A) X := by
  simp [rightMul, Matrix.mul_assoc]

/-- Left and right multiplication commute as operators. -/
theorem leftMul_rightMul_commute (A B X : MatrixQuantumCarrier) :
    leftMul A (rightMul B X) = rightMul B (leftMul A X) := by
  simp [leftMul, rightMul, Matrix.mul_assoc]

/-- Left-operator commutator acts by the matrix commutator. -/
theorem leftMul_commutator_action (A B X : MatrixQuantumCarrier) :
    leftMul A (leftMul B X) - leftMul B (leftMul A X) =
      leftMul (matrixComm A B) X := by
  unfold leftMul matrixComm
  rw [sub_mul]
  simp [Matrix.mul_assoc]

/-- Right-operator commutator acts by the opposite matrix commutator. -/
theorem rightMul_commutator_action (A B X : MatrixQuantumCarrier) :
    rightMul A (rightMul B X) - rightMul B (rightMul A X) =
      rightMul (matrixComm B A) X := by
  unfold rightMul matrixComm
  rw [mul_sub]
  simp [Matrix.mul_assoc]

/-- Matrix unit `E₁₁`. -/
def E11 : MatrixQuantumCarrier := !![1, 0; 0, 0]

/-- Matrix unit `E₁₂`. -/
def E12 : MatrixQuantumCarrier := !![0, 1; 0, 0]

/-- Matrix unit `E₂₁`. -/
def E21 : MatrixQuantumCarrier := !![0, 0; 1, 0]

/-- Matrix unit `E₂₂`. -/
def E22 : MatrixQuantumCarrier := !![0, 0; 0, 1]

/-- `E₁₁` has joint eigenvalues `(1,1)` for left/right `σ₃`. -/
theorem sigma3_E11_joint_eigen :
    leftMul UnifiedMatrixBasis.σ₃ E11 = E11 ∧
    rightMul UnifiedMatrixBasis.σ₃ E11 = E11 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [leftMul, rightMul, E11, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₁₂` has joint eigenvalues `(1,-1)` for left/right `σ₃`. -/
theorem sigma3_E12_joint_eigen :
    leftMul UnifiedMatrixBasis.σ₃ E12 = E12 ∧
    rightMul UnifiedMatrixBasis.σ₃ E12 = -E12 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [leftMul, rightMul, E12, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₂₁` has joint eigenvalues `(-1,1)` for left/right `σ₃`. -/
theorem sigma3_E21_joint_eigen :
    leftMul UnifiedMatrixBasis.σ₃ E21 = -E21 ∧
    rightMul UnifiedMatrixBasis.σ₃ E21 = E21 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [leftMul, rightMul, E21, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₂₂` has joint eigenvalues `(-1,-1)` for left/right `σ₃`. -/
theorem sigma3_E22_joint_eigen :
    leftMul UnifiedMatrixBasis.σ₃ E22 = -E22 ∧
    rightMul UnifiedMatrixBasis.σ₃ E22 = -E22 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [leftMul, rightMul, E22, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- Diagonal matrix units are idempotent projectors. -/
theorem matrixUnit_projectors : E11 * E11 = E11 ∧ E22 * E22 = E22 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [E11, E22, Matrix.mul_apply, Fin.sum_univ_two]

/-- Off-diagonal matrix units are square-zero nilpotents. -/
theorem matrixUnit_nilpotents : E12 * E12 = 0 ∧ E21 * E21 = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [E12, E21, Matrix.mul_apply, Fin.sum_univ_two]

/-- Basic matrix-unit products. -/
theorem matrixUnit_cross_products : E12 * E21 = E11 ∧ E21 * E12 = E22 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [E11, E12, E21, E22, Matrix.mul_apply, Fin.sum_univ_two]

/-- `E₁₁` in the Pauli basis. -/
theorem E11_pauli_decomposition :
    E11 = (1 / 2 : ℂ) • (UnifiedMatrixBasis.I₂ + UnifiedMatrixBasis.σ₃) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [E11, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₃]

/-- `E₂₂` in the Pauli basis. -/
theorem E22_pauli_decomposition :
    E22 = (1 / 2 : ℂ) • (UnifiedMatrixBasis.I₂ - UnifiedMatrixBasis.σ₃) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [E22, UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₃]

/-- `E₁₂` in the Pauli basis. -/
theorem E12_pauli_decomposition :
    E12 = (1 / 2 : ℂ) •
      (UnifiedMatrixBasis.σ₁ + Complex.I • UnifiedMatrixBasis.σ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E12, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂]
    <;> norm_num <;> simp [Complex.I_sq]

/-- `E₂₁` in the Pauli basis. -/
theorem E21_pauli_decomposition :
    E21 = (1 / 2 : ℂ) •
      (UnifiedMatrixBasis.σ₁ - Complex.I • UnifiedMatrixBasis.σ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E21, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂]
    <;> norm_num <;> simp [Complex.I_sq]

/-- `E₁₁` as a complex-biquaternion matrix representative. -/
theorem E11_biquat_decomposition :
    E11 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      (1 / 2) 0 0 (Complex.I / 2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E11, InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃]
    <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- `E₂₂` as a complex-biquaternion matrix representative. -/
theorem E22_biquat_decomposition :
    E22 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      (1 / 2) 0 0 (-Complex.I / 2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E22, InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃]
    <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- `E₁₂` as a complex-biquaternion matrix representative. -/
theorem E12_biquat_decomposition :
    E12 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      0 (Complex.I / 2) (-1 / 2) 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E12, InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃]
    <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- `E₂₁` as a complex-biquaternion matrix representative. -/
theorem E21_biquat_decomposition :
    E21 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      0 (Complex.I / 2) (1 / 2) 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E21, InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁, UnifiedMatrixBasis.σ₂,
      UnifiedMatrixBasis.σ₃]
    <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- Root-vector relation `[σ₃,E₁₂]=2E₁₂`. -/
theorem sigma3_comm_E12 :
    matrixComm UnifiedMatrixBasis.σ₃ E12 = (2 : ℂ) • E12 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [matrixComm, E12, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Root-vector relation `[σ₃,E₂₁]=-2E₂₁`. -/
theorem sigma3_comm_E21 :
    matrixComm UnifiedMatrixBasis.σ₃ E21 = (-2 : ℂ) • E21 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [matrixComm, E21, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Root-vector relation `[E₁₂,E₂₁]=σ₃`. -/
theorem E12_comm_E21 :
    matrixComm E12 E21 = UnifiedMatrixBasis.σ₃ := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [matrixComm, E11, E12, E21, E22, UnifiedMatrixBasis.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- Repaired theorem-safe Chapter 6 finite operator/eigenoperator packet. -/
theorem repaired_MD006_operator_eigenoperator_packet (A B X : MatrixQuantumCarrier) :
    leftMul A (rightMul B X) = rightMul B (leftMul A X) ∧
    leftMul A (leftMul B X) - leftMul B (leftMul A X) = leftMul (matrixComm A B) X ∧
    rightMul A (rightMul B X) - rightMul B (rightMul A X) = rightMul (matrixComm B A) X ∧
    leftMul UnifiedMatrixBasis.σ₃ E12 = E12 ∧
    rightMul UnifiedMatrixBasis.σ₃ E12 = -E12 ∧
    E12 * E21 = E11 ∧
    E21 * E12 = E22 ∧
    E11 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      (1 / 2) 0 0 (Complex.I / 2) ∧
    E12 = InfoGeometry.Physics.MD003IsomorphicRepresentations.biquatMatrix
      0 (Complex.I / 2) (-1 / 2) 0 ∧
    matrixComm UnifiedMatrixBasis.σ₃ E12 = (2 : ℂ) • E12 ∧
    matrixComm UnifiedMatrixBasis.σ₃ E21 = (-2 : ℂ) • E21 ∧
    matrixComm E12 E21 = UnifiedMatrixBasis.σ₃ := by
  exact ⟨leftMul_rightMul_commute A B X,
    leftMul_commutator_action A B X,
    rightMul_commutator_action A B X,
    sigma3_E12_joint_eigen.1,
    sigma3_E12_joint_eigen.2,
    matrixUnit_cross_products.1,
    matrixUnit_cross_products.2,
    E11_biquat_decomposition,
    E12_biquat_decomposition,
    sigma3_comm_E12,
    sigma3_comm_E21,
    E12_comm_E21⟩

end InfoGeometry.Physics.MD006OperatorEigenoperators

end noncomputable section
