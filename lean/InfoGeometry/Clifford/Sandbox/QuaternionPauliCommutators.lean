import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Standard Quaternion Pauli Commutators and Comparison with Split-Quaternions

This file formalizes the standard quaternion algebra $\mathbb{H}$ as $2 \times 2$
complex matrices using the Pauli matrices scaled by the complex imaginary unit $i$:

```
  I = -i σ_x = [[0, -i], [-i, 0]]
  J = -i σ_y = [[0, -1], [1, 0]]
  K = -i σ_z = [[-i, 0], [0, i]]
```

It proves the standard division algebra signature $(-,-,-)$ via commutators and
anticommutators, and contrasts it directly with the split-quaternion signature
$(-,+,+)$ formalized in `SplitQuaternionPauliCommutators.lean`.
-/

set_option autoImplicit false

open scoped Matrix

namespace InfoGeometry.Clifford.Sandbox.QuaternionPauliCommutators

noncomputable section

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Standard quaternion basis unit `I = -i σ_x`. -/
def qI : Mat2C :=
  !![0, -Complex.I; -Complex.I, 0]

/-- Standard quaternion basis unit `J = -i σ_y`. -/
def qJ : Mat2C :=
  !![0, -1; 1, 0]

/-- Standard quaternion basis unit `K = -i σ_z`. -/
def qK : Mat2C :=
  !![-Complex.I, 0; 0, Complex.I]

/-! ## Squaring Relations (Signature) -/

@[simp] theorem qI_sq : qI * qI = -(1 : Mat2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem qJ_sq : qJ * qJ = -(1 : Mat2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem qK_sq : qK * qK = -(1 : Mat2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qK, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Product Relations -/

theorem qI_mul_qJ : qI * qJ = qK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

theorem qJ_mul_qI : qJ * qI = -qK := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

theorem qJ_mul_qK : qJ * qK = qI := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

theorem qK_mul_qJ : qK * qJ = -qI := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

theorem qK_mul_qI : qK * qI = qJ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

theorem qI_mul_qK : qI * qK = -qJ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Commutators `[A, B] = AB - BA` -/

def commutator (A B : Mat2C) : Mat2C :=
  A * B - B * A

theorem comm_qI_qJ : commutator qI qJ = (2 : ℂ) • qK := by
  simp [commutator, qI_mul_qJ, qJ_mul_qI, two_smul]

theorem comm_qJ_qK : commutator qJ qK = (2 : ℂ) • qI := by
  simp [commutator, qJ_mul_qK, qK_mul_qJ, two_smul]

theorem comm_qK_qI : commutator qK qI = (2 : ℂ) • qJ := by
  simp [commutator, qK_mul_qI, qI_mul_qK, two_smul]

/-! ## Anticommutators `{A, B} = AB + BA` -/

def anticommutator (A B : Mat2C) : Mat2C :=
  A * B + B * A

theorem anticomm_qI_qI : anticommutator qI qI = -((2 : ℂ) • (1 : Mat2C)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, qI, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] <;> ring

theorem anticomm_qJ_qJ : anticommutator qJ qJ = -((2 : ℂ) • (1 : Mat2C)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, qJ, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] <;> ring

theorem anticomm_qK_qK : anticommutator qK qK = -((2 : ℂ) • (1 : Mat2C)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, qK, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] <;> ring

theorem anticomm_qI_qJ : anticommutator qI qJ = 0 := by
  simp [anticommutator, qI_mul_qJ, qJ_mul_qI]

theorem anticomm_qJ_qK : anticommutator qJ qK = 0 := by
  simp [anticommutator, qJ_mul_qK, qK_mul_qJ]

theorem anticomm_qK_qI : anticommutator qK qI = 0 := by
  simp [anticommutator, qK_mul_qI, qI_mul_qK]

/-! ## Consolidated Quaternion Algebra Packet -/

theorem quaternion_pauli_algebra :
    -- Squaring relations (signature: all three are negative)
    qI * qI = -(1 : Mat2C)
    ∧ qJ * qJ = -(1 : Mat2C)
    ∧ qK * qK = -(1 : Mat2C)
    -- Commutators
    ∧ commutator qI qJ = (2 : ℂ) • qK
    ∧ commutator qJ qK = (2 : ℂ) • qI
    ∧ commutator qK qI = (2 : ℂ) • qJ
    -- Anticommutators (all cross terms vanish)
    ∧ anticommutator qI qJ = 0
    ∧ anticommutator qJ qK = 0
    ∧ anticommutator qK qI = 0 :=
  ⟨qI_sq, qJ_sq, qK_sq,
   comm_qI_qJ, comm_qJ_qK, comm_qK_qI,
   anticomm_qI_qJ, anticomm_qJ_qK, anticomm_qK_qI⟩

end

end InfoGeometry.Clifford.Sandbox.QuaternionPauliCommutators
