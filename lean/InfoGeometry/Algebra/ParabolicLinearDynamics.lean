import InfoGeometry.Algebra.MatrixCyclotomics

noncomputable section

namespace InfoGeometry.Algebra.ParabolicLinearDynamics

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.MatrixCyclotomics

def differential (parameter : ℝ) : Mat2 →ₗ[ℝ] Mat2 :=
  LinearMap.mulLeft ℝ (NPart parameter - 1)

theorem differential_squared (parameter : ℝ) (state : Mat2) :
    differential parameter (differential parameter state) = 0 := by
  change (NPart parameter - 1) * ((NPart parameter - 1) * state) = 0
  rw [← mul_assoc, ← pow_two, shear_unipotent, zero_mul]

theorem differential_range_le_ker (parameter : ℝ) :
    LinearMap.range (differential parameter) ≤ LinearMap.ker (differential parameter) := by
  rintro state ⟨preimage, rfl⟩
  exact differential_squared parameter preimage

def chiralSwitch : Mat2 →ₗ[ℝ] Mat2 :=
  (LinearMap.mulRight ℝ J1).comp (LinearMap.mulLeft ℝ J1)

theorem chiralSwitch_involutive : Function.Involutive chiralSwitch := by
  intro state
  change J1 * (J1 * state * J1) * J1 = state
  calc
    J1 * (J1 * state * J1) * J1 = (J1 * J1) * state * (J1 * J1) := by
      simp only [mul_assoc]
    _ = state := by rw [J1_sq]; simp

theorem chiralSwitch_mul (first second : Mat2) :
    chiralSwitch (first * second) = chiralSwitch first * chiralSwitch second := by
  change J1 * (first * second) * J1 = (J1 * first * J1) * (J1 * second * J1)
  symm
  calc
    (J1 * first * J1) * (J1 * second * J1) =
        J1 * first * (J1 * J1) * second * J1 := by simp only [mul_assoc]
    _ = J1 * (first * second) * J1 := by rw [J1_sq]; simp [mul_assoc]

theorem APart_add (first second : ℝ) :
    APart (first + second) = APart first * APart second := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [APart, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add] <;> ring

theorem APart_zero : APart 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [APart]

theorem APart_mul_neg (parameter : ℝ) : APart parameter * APart (-parameter) = 1 := by
  rw [← APart_add, add_neg_cancel, APart_zero]

def flow (parameter : ℝ) : Mat2 →ₗ[ℝ] Mat2 :=
  LinearMap.mulLeft ℝ (APart parameter)

theorem flow_add (first second : ℝ) (state : Mat2) :
    flow (first + second) state = flow first (flow second state) := by
  change APart (first + second) * state = APart first * (APart second * state)
  rw [APart_add, mul_assoc]

theorem flow_reversible (parameter : ℝ) (state : Mat2) :
    flow (-parameter) (flow parameter state) = state := by
  rw [← flow_add]
  simp [flow, APart_zero]

def combinedOperator (shearParameter timeParameter : ℝ) : Mat2 →ₗ[ℝ] Mat2 :=
  differential shearParameter + chiralSwitch + flow timeParameter

theorem combinedOperator_static (state : Mat2) :
    combinedOperator 0 0 state = chiralSwitch state + state := by
  change (NPart 0 - 1) * state + chiralSwitch state + APart 0 * state =
    chiralSwitch state + state
  rw [(NPart_eq_one_iff 0).mpr rfl, APart_zero]
  simp

theorem combinedOperator_zero (shearParameter timeParameter : ℝ) :
    combinedOperator shearParameter timeParameter 0 = 0 :=
  map_zero _

def symmetricDifferentialMatrix (parameter : ℝ) : Mat2 :=
  (NPart parameter - 1) + Matrix.transpose (NPart parameter - 1)

theorem symmetricDifferentialMatrix_transpose (parameter : ℝ) :
    Matrix.transpose (symmetricDifferentialMatrix parameter) =
      symmetricDifferentialMatrix parameter := by
  simp [symmetricDifferentialMatrix, Matrix.transpose_add,
    Matrix.transpose_transpose, add_comm]

theorem symmetricDifferentialMatrix_square (parameter : ℝ) :
    symmetricDifferentialMatrix parameter ^ 2 = parameter ^ 2 • (1 : Mat2) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [symmetricDifferentialMatrix, NPart, Matrix.transpose, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem no_two_orthogonal_matrix_isometries (first second : Mat2)
    (hfirst : Matrix.transpose first * first = 1)
    (hsecond : Matrix.transpose second * second = 1)
    (horthogonal : Matrix.transpose first * second = 0) : False := by
  have hright : first * Matrix.transpose first = 1 :=
    mul_eq_one_comm.mp hfirst
  have hzero : second = 0 := by
    calc
      second = (first * Matrix.transpose first) * second := by
        rw [hright, one_mul]
      _ = first * (Matrix.transpose first * second) := mul_assoc _ _ _
      _ = 0 := by rw [horthogonal, mul_zero]
  simpa [hzero] using hsecond

end InfoGeometry.Algebra.ParabolicLinearDynamics
