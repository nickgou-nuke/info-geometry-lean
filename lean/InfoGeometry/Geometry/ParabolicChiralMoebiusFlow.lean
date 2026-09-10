import InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.RealMoebiusAction

namespace InfoGeometry.Geometry.ParabolicChiralMoebiusFlow

open InfoGeometry.Geometry.MoebiusChiralGeneratorClassification
open InfoGeometry.Geometry.RealUpperHalfPlane

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

def sheetReflection : Mat2 := !![(0 : ℝ), 1; 1, 0]

def upperParabolic (T : ℝ) : SL2R :=
  ⟨!![(1 : ℝ), T; 0, 1], by
    simp [Matrix.det_fin_two]⟩

def lowerParabolic (T : ℝ) : SL2R :=
  ⟨!![(1 : ℝ), 0; T, 1], by
    simp [Matrix.det_fin_two]⟩

theorem upperParabolic_x (T : ℝ) (τ : RealUpperHalfPlane) :
    ((upperParabolic T) • τ).x = τ.x + T := by
  simp [upperParabolic, RealUpperHalfPlane.smul_def,
    RealUpperHalfPlane.moebius, RealUpperHalfPlane.a,
    RealUpperHalfPlane.b, RealUpperHalfPlane.c,
    RealUpperHalfPlane.d, RealUpperHalfPlane.denomSq]

theorem upperParabolic_y (T : ℝ) (τ : RealUpperHalfPlane) :
    ((upperParabolic T) • τ).y = τ.y := by
  simp [upperParabolic, RealUpperHalfPlane.smul_def,
    RealUpperHalfPlane.moebius, RealUpperHalfPlane.a,
    RealUpperHalfPlane.b, RealUpperHalfPlane.c,
    RealUpperHalfPlane.d, RealUpperHalfPlane.denomSq]

theorem sheetReflection_conjugates_parabolics (T : ℝ) :
    sheetReflection * (upperParabolic T : Mat2) * sheetReflection =
      (lowerParabolic T : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetReflection, upperParabolic, lowerParabolic,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetReflection_conjugates_nilpotents :
    sheetReflection * NPlus * sheetReflection = NMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetReflection, NPlus, NMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Geometry.ParabolicChiralMoebiusFlow
