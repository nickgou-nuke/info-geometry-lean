import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Geometry.MoebiusChiralGeneratorClassification

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

def H : Mat2 := !![(1 : ℝ), 0; 0, -1]

def NPlus : Mat2 := !![(0 : ℝ), 1; 0, 0]

def NMinus : Mat2 := !![(0 : ℝ), 0; 1, 0]

def generator (h x y : ℝ) : Mat2 :=
  !![h, x; y, -h]

theorem H_mul_NPlus : H * NPlus - NPlus * H = (2 : ℝ) • NPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, NPlus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem H_mul_NMinus : H * NMinus - NMinus * H = (-2 : ℝ) • NMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, NMinus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem NPlus_mul_NMinus_sub_NMinus_mul_NPlus :
    NPlus * NMinus - NMinus * NPlus = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, NPlus, NMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem NPlus_sq : NPlus * NPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem NMinus_sq : NMinus * NMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem generator_sq (h x y : ℝ) :
    generator h x y * generator h x y = (h ^ 2 + x * y) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · ring
  · ring
  · ring
  · ring

theorem generator_det (h x y : ℝ) :
    (generator h x y).det = -(h ^ 2 + x * y) := by
  simp [generator, Matrix.det_fin_two]
  ring

end InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
