import Mathlib

open Matrix

abbrev Q := ℚ

def zeroMatrixA : Matrix (Fin 3) (Fin 3) Q := 0
def zeroMatrixB : Matrix (Fin 3) (Fin 3) Q := 0

def zeroCommutatorDeterminant : Q :=
  det (⁅zeroMatrixA, zeroMatrixB⁆)

lemma zeroCommutator_det_trace_cube_identity :
    zeroCommutatorDeterminant = (1 / 3 : Q) * trace (⁅zeroMatrixA, zeroMatrixB⁆ ^ 3) := by
  simp [zeroCommutatorDeterminant, zeroMatrixA, zeroMatrixB]
  exact Matrix.det_zero ⟨0⟩
