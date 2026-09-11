import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix

namespace Test4

abbrev Q := ℚ

def zeroMatrixA : Matrix (Fin 3) (Fin 3) Q := 0
def zeroMatrixB : Matrix (Fin 3) (Fin 3) Q := 0

def zeroCommutatorDeterminant : Q :=
  det (⁅zeroMatrixA, zeroMatrixB⁆)

lemma zeroCommutator_det_trace_cube_identity :
    zeroCommutatorDeterminant = (1 / 3 : Q) * trace (⁅zeroMatrixA, zeroMatrixB⁆ ^ 3) := by
  change det ((0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0) =
    (1 / 3 : Q) * trace (((0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0) ^ 3)
  have hz : (0 : Matrix (Fin 3) (Fin 3) Q) * 0 - 0 * 0 = 0 := by
    simp
  rw [hz, Matrix.det_zero (Nonempty.intro (0 : Fin 3))]
  simp

end Test4
