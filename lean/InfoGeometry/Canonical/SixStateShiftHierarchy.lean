import Mathlib.LinearAlgebra.Matrix.Vec
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

open scoped Matrix

namespace InfoGeometry.Canonical.SixStateShiftHierarchy

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

noncomputable section

def colorBasisVector (a : Fin 3) : Fin 3 → ℂ := Pi.single a 1

theorem colorShift_mulVec_colorBasisVector (a : Fin 3) :
    colorShift *ᵥ colorBasisVector a =
      colorBasisVector (a + 1) := by
  fin_cases a <;>
    funext i <;>
    fin_cases i <;>
    simp [colorBasisVector, colorShift, Matrix.mulVec,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem colorShift_cubed_mulVec_colorBasisVector (a : Fin 3) :
    colorShift ^ 3 *ᵥ colorBasisVector a = colorBasisVector a := by
  rw [colorShift_cubed]
  simp

end
end InfoGeometry.Canonical.SixStateShiftHierarchy
