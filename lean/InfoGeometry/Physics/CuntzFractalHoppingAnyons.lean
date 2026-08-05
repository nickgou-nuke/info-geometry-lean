import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Physics

/-- Four finite states: three boundary labels and one distinguished defect state. -/
abbrev FractalState := Fin 4

/-- A real hopping operator on the finite state space. -/
abbrev HoppingOp := Matrix FractalState FractalState ℝ

/-- The transposition of the first two boundary labels. -/
def braidSigma01 : HoppingOp :=
  ![![0, 1, 0, 0],
    ![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

/-- The transposition of the second and third boundary labels. -/
def braidSigma12 : HoppingOp :=
  ![![1, 0, 0, 0],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![0, 0, 0, 1]]

def defectVector : Matrix FractalState (Fin 1) ℝ :=
  ![![0], ![0], ![0], ![1]]

theorem braidSigma01_defect_invariant :
    braidSigma01 * defectVector = defectVector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [braidSigma01, defectVector, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem braidSigma12_defect_invariant :
    braidSigma12 * defectVector = defectVector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [braidSigma12, defectVector, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The two concrete adjacent transpositions satisfy the Artin braid relation. -/
theorem braidSigma01_braidSigma12_braidSigma01 :
    braidSigma01 * braidSigma12 * braidSigma01 =
      braidSigma12 * braidSigma01 * braidSigma12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [braidSigma01, braidSigma12, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem fractal_hopping_anyon_synthesis :
    (braidSigma01 * defectVector = defectVector) ∧
    (braidSigma12 * defectVector = defectVector) ∧
    (braidSigma01 * braidSigma12 * braidSigma01 =
      braidSigma12 * braidSigma01 * braidSigma12) :=
  ⟨braidSigma01_defect_invariant, braidSigma12_defect_invariant,
    braidSigma01_braidSigma12_braidSigma01⟩

end InfoGeometry.Physics
