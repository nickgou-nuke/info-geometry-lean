import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pauli quaternion versus split-quaternion matrix packets

This file records the finite `2 × 2` matrix facts behind the informal slogan
"replace the complex Pauli imaginary by a hyperbolic unit".  The result is
kept theorem-honest: it proves concrete matrix commutator and anticommutator
identities for

* the standard quaternion units represented in `M₂(ℂ)` by `-i σ₁`, `-i σ₂`,
  `-i σ₃`, and
* the split-quaternion units represented in `M₂(ℝ)` by the existing owner
  `SplitQuaternionMatrices.sqI`, `sqJ`, and `sqK`.

No analytic, physical, or classification statement is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.PauliQuaternionSplitComparison

open Matrix
open scoped Matrix
open InfoGeometryCore

/-- Complex `2 × 2` matrices. -/
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Matrix commutator. -/
def commC (A B : M2C) : M2C := A * B - B * A

/-- Matrix anticommutator. -/
def anticommC (A B : M2C) : M2C := A * B + B * A

/-- Quaternion unit `I = -i σ₁`. -/
def quatI : M2C :=
  !![0, -Complex.I;
     -Complex.I, 0]

/-- Quaternion unit `J = -i σ₂`. -/
def quatJ : M2C :=
  !![0, -1;
     1, 0]

/-- Quaternion unit `K = -i σ₃`. -/
def quatK : M2C :=
  !![-Complex.I, 0;
     0, Complex.I]

@[simp] theorem quatI_sq : quatI * quatI = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem quatJ_sq : quatJ * quatJ = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [quatJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatK_sq : quatK * quatK = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatK, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem quatI_mul_quatJ : quatI * quatJ = quatK := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatJ_mul_quatI : quatJ * quatI = -quatK := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatJ_mul_quatK : quatJ * quatK = quatI := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatK_mul_quatJ : quatK * quatJ = -quatI := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatK_mul_quatI : quatK * quatI = quatJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem quatI_mul_quatK : quatI * quatK = -quatJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, Matrix.mul_apply, Fin.sum_univ_two]

/-- The standard quaternion commutator packet. -/
theorem quaternion_commutator_packet :
    commC quatI quatJ = (2 : ℂ) • quatK ∧
    commC quatJ quatK = (2 : ℂ) • quatI ∧
    commC quatK quatI = (2 : ℂ) • quatJ := by
  simp [commC, sub_eq_add_neg, two_smul]

/-- The standard quaternion anticommutator packet. -/
theorem quaternion_anticommutator_packet :
    anticommC quatI quatI = (-2 : ℂ) • (1 : M2C) ∧
    anticommC quatJ quatJ = (-2 : ℂ) • (1 : M2C) ∧
    anticommC quatK quatK = (-2 : ℂ) • (1 : M2C) ∧
    anticommC quatI quatJ = 0 ∧
    anticommC quatJ quatK = 0 ∧
    anticommC quatK quatI = 0 := by
  simp [anticommC, two_smul]

namespace Split

open SplitQuaternionMatrices

/-- Matrix commutator in the real split-quaternion matrix owner. -/
def commR (A B : M2R) : M2R := A * B - B * A

/-- Matrix anticommutator in the real split-quaternion matrix owner. -/
def anticommR (A B : M2R) : M2R := A * B + B * A

/-- The split-quaternion commutator packet with signature-dependent signs. -/
theorem split_quaternion_commutator_packet :
    commR sqI sqJ = (2 : ℝ) • sqK ∧
    commR sqJ sqK = (-2 : ℝ) • sqI ∧
    commR sqK sqI = (2 : ℝ) • sqJ := by
  simp [commR, sub_eq_add_neg, two_smul]

/-- The split-quaternion anticommutator packet exposing signature `(-,+,+)`. -/
theorem split_quaternion_anticommutator_packet :
    anticommR sqI sqI = (-2 : ℝ) • (1 : M2R) ∧
    anticommR sqJ sqJ = (2 : ℝ) • (1 : M2R) ∧
    anticommR sqK sqK = (2 : ℝ) • (1 : M2R) ∧
    anticommR sqI sqJ = 0 ∧
    anticommR sqJ sqK = 0 ∧
    anticommR sqK sqI = 0 := by
  simp [anticommR, two_smul]

end Split

end InfoGeometry.Algebra.PauliQuaternionSplitComparison

end
