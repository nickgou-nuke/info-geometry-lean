import Mathlib
import InfoGeometry.Exceptional.SquareZeroShearFlow

/-!
# GAP-to-Lean readback for the square-zero shear

The GAP certificate uses rows and columns `1,2`; Lean uses `Fin 2`.  The
matrix below is the explicit row-major translation, and the theorem is
reproved in Lean rather than imported from GAP.
-/

namespace InfoGeometry.Exceptional.SquareZeroShear

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def gapShearGenerator : Mat2 := !![0, 1; 0, 0]

theorem gapShearGenerator_sq : gapShearGenerator * gapShearGenerator = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gapShearGenerator, Matrix.mul_apply, Fin.sum_univ_two]

theorem gapShearGenerator_readback :
    gapShearGenerator * gapShearGenerator = (0 : Mat2) :=
  gapShearGenerator_sq

theorem gapShearGenerator_shear_law (s t : ℝ) :
    shear gapShearGenerator s * shear gapShearGenerator t =
      shear gapShearGenerator (s + t) := by
  exact shear_mul gapShearGenerator gapShearGenerator_sq s t

end InfoGeometry.Exceptional.SquareZeroShear
