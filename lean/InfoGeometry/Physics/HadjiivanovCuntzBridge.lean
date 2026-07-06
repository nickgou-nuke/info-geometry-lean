import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

/-!
# InfoGeometry.Physics.HadjiivanovCuntzBridge

Minimal owner-facing bridge for the finite Hadjiivanov logarithmic block used by
`HadjiivanovBostConnesBridge`.

This file does not claim a full Cuntz-algebra realization. It only packages the
existing rank-two nilpotent Jordan block from `Clifford.LogCftMonodromy` into a
small record with a named `matrix` field, so downstream files can state and use
trace computations honestly.
-/

namespace InfoGeometry.Physics.Hadjiivanov

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- Finite packaged logarithmic block with an explicit matrix carrier. -/
structure LogBlock (R : Type*) [Zero R] [One R] where
  matrix : Matrix (Fin 2) (Fin 2) R

/--
The standard Hadjiivanov logarithmic block is the square-zero upper Jordan shear
`[[0,1],[0,0]]`.
-/
def standardLogBlock (R : Type*) [Zero R] [One R] : LogBlock R where
  matrix := jordanNilpotent

@[simp] theorem standardLogBlock_matrix (R : Type*) [Zero R] [One R] :
    (standardLogBlock R).matrix = (jordanNilpotent : Matrix (Fin 2) (Fin 2) R) := rfl

@[simp] theorem standardLogBlock_trace (R : Type*) [CommRing R] :
    Matrix.trace (standardLogBlock R).matrix = 0 := by
  simp [standardLogBlock, Matrix.trace_fin_two, jordanNilpotent]

end InfoGeometry.Physics.Hadjiivanov
