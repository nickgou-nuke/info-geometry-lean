import Mathlib
import InfoGeometry.Canonical.ProjectiveUnitary6

namespace InfoGeometry.Canonical.SixStateProjectiveMobiusBridge

open scoped Matrix

abbrev StateMatrix := Matrix (Fin 6) (Fin 6) ℂ
abbrev U6 := ProjectiveUnitary6.U6
abbrev PU6 := ProjectiveUnitary6.PU6

def thetaMatrix : StateMatrix :=
  !![(0 : ℂ), 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0]

def flowMatrix : StateMatrix :=
  !![(1 : ℂ), 0, 0, 0, 0, 0;
     0, Complex.I, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -Complex.I, 0;
     0, 0, 0, 0, 0, -1]

def inverseFlowMatrix : StateMatrix :=
  !![(1 : ℂ), 0, 0, 0, 0, 0;
     0, -Complex.I, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, Complex.I, 0;
     0, 0, 0, 0, 0, -1]

theorem thetaMatrix_sq : thetaMatrix * thetaMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaMatrix, Matrix.mul_apply, Fin.sum_univ_six]

theorem flowMatrix_mul_inverseFlowMatrix :
    flowMatrix * inverseFlowMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flowMatrix, inverseFlowMatrix, Matrix.mul_apply, Fin.sum_univ_six]

theorem thetaMatrix_conj_flowMatrix :
    thetaMatrix * flowMatrix * thetaMatrix = inverseFlowMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaMatrix, flowMatrix, inverseFlowMatrix, Matrix.mul_apply,
      Fin.sum_univ_six]

theorem thetaMatrix_mem_unitary : thetaMatrix ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaMatrix, Matrix.mul_apply,
      Fin.sum_univ_six]

theorem flowMatrix_mem_unitary : flowMatrix ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flowMatrix,
      Matrix.mul_apply, Fin.sum_univ_six]

theorem inverseFlowMatrix_mem_unitary :
    inverseFlowMatrix ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseFlowMatrix,
      Matrix.mul_apply, Fin.sum_univ_six]

noncomputable def theta6 : U6 :=
  ⟨thetaMatrix, thetaMatrix_mem_unitary⟩

noncomputable def flow6 : U6 :=
  ⟨flowMatrix, flowMatrix_mem_unitary⟩

noncomputable def inverseFlow6 : U6 :=
  ⟨inverseFlowMatrix, inverseFlowMatrix_mem_unitary⟩

@[simp] theorem theta6_val : (theta6 : StateMatrix) = thetaMatrix := rfl

@[simp] theorem flow6_val : (flow6 : StateMatrix) = flowMatrix := rfl

theorem theta6_sq : theta6 * theta6 = 1 := by
  apply Subtype.ext
  exact thetaMatrix_sq

theorem flow6_mul_inverseFlow6 : flow6 * inverseFlow6 = 1 := by
  apply Subtype.ext
  change flowMatrix * inverseFlowMatrix = 1
  exact flowMatrix_mul_inverseFlowMatrix

theorem flow6_inv : flow6⁻¹ = inverseFlow6 :=
  inv_eq_of_mul_eq_one_right flow6_mul_inverseFlow6

theorem theta6_conj_flow6 :
    theta6 * flow6 * theta6⁻¹ = flow6⁻¹ := by
  have htheta : theta6⁻¹ = theta6 :=
    inv_eq_of_mul_eq_one_right theta6_sq
  rw [htheta, flow6_inv]
  apply Subtype.ext
  change thetaMatrix * flowMatrix * thetaMatrix = inverseFlowMatrix
  exact thetaMatrix_conj_flowMatrix

theorem theta6_projective_conj_flow6 :
    ProjectiveUnitary6.toPU6 theta6 * ProjectiveUnitary6.toPU6 flow6 *
        (ProjectiveUnitary6.toPU6 theta6)⁻¹ =
      (ProjectiveUnitary6.toPU6 flow6)⁻¹ := by
  exact ProjectiveUnitary6.projective_conjugation_relation
    theta6 flow6 1 (Subgroup.one_mem _) (by simpa using theta6_conj_flow6)

end InfoGeometry.Canonical.SixStateProjectiveMobiusBridge
