import Mathlib.Tactic
open Matrix
namespace InfoGeometry.Physics.GellMannSU3

def gl3 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
def gl8 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, -2]
def gl1 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
def gl2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]
def gl4 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]
def gl5 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0]
def gl6 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]
def gl7 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]


theorem gl3_comm_gl8 : gl3 * gl8 = gl8 * gl3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl3, gl8]

theorem gl1_comm_gl2 : gl1 * gl2 - gl2 * gl1 = (2 * Complex.I) • gl3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl2, gl3, Matrix.smul_apply] <;> ring

/-- Cartan action on the real `λ₁` root direction.  This avoids any matrix-level
basis ambiguity: the commutator is the imaginary partner `λ₂`. -/
theorem gl1_comm_gl3 : gl1 * gl3 - gl3 * gl1 = (-2 * Complex.I) • gl2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gl1, gl2, gl3, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp [Complex.I_mul_I]

theorem gl1_comm_gl6 : gl1 * gl6 - gl6 * gl1 = Complex.I • gl5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl5, gl6, Matrix.smul_apply]

theorem gl1_comm_gl7 : gl1 * gl7 - gl7 * gl1 = (-Complex.I) • gl4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl4, gl7, Matrix.smul_apply]

theorem gl2_comm_gl3 : gl2 * gl3 - gl3 * gl2 = (2 * Complex.I) • gl1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl2, gl3, Matrix.smul_apply] <;> ring

theorem gl2_comm_gl6 : gl2 * gl6 - gl6 * gl2 = (-Complex.I) • gl4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, gl4, gl6, Matrix.smul_apply]

theorem gl2_comm_gl7 : gl2 * gl7 - gl7 * gl2 = (-Complex.I) • gl5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, gl5, gl7, Matrix.smul_apply]

theorem gl3_comm_gl4 : gl3 * gl4 - gl4 * gl3 = Complex.I • gl5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl3, gl4, gl5, Matrix.smul_apply]

theorem gl3_comm_gl5 : gl3 * gl5 - gl5 * gl3 = (-Complex.I) • gl4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl3, gl4, gl5, Matrix.smul_apply]

theorem gl4_comm_gl6 : gl4 * gl6 - gl6 * gl4 = Complex.I • gl2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, gl4, gl6, Matrix.smul_apply]

theorem gl4_comm_gl7 : gl4 * gl7 - gl7 * gl4 = Complex.I • gl1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl4, gl7, Matrix.smul_apply]

theorem gl5_comm_gl6 : gl5 * gl6 - gl6 * gl5 = (-Complex.I) • gl1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl1, gl5, gl6, Matrix.smul_apply]

theorem gl5_comm_gl7 : gl5 * gl7 - gl7 * gl5 = Complex.I • gl2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl2, gl5, gl7, Matrix.smul_apply]

theorem gl5_comm_gl8 : gl5 * gl8 - gl8 * gl5 = (3 * Complex.I) • gl4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gl4, gl5, gl8, Matrix.smul_apply] <;> ring

/-- Cartan action of `λ₈` on the real `λ₄` root direction. -/
theorem gl4_comm_gl8 : gl4 * gl8 - gl8 * gl4 = (-3 * Complex.I) • gl5 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gl4, gl5, gl8, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_three] <;>
    ring_nf <;> simp [Complex.I_mul_I]

end InfoGeometry.Physics.GellMannSU3
