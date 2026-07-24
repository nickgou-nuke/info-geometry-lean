import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.KatzSarnakDensity

open Matrix

/-!
# Finite projector trace readout

This module proves a concrete `8 × 8` integer-matrix trace calculation.  It
does not identify a Drazin projector with Katz--Sarnak low-lying zeros or prove
any L-function density theorem.
-/

/-- The topological boundary projector P_zero (complement of the Drazin core). 
In our 8x8 active/ghost sector formulation, it isolates the singular topological boundary. -/
def P_zero : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

/-- The Drazin core P_D. The complement to P_zero. -/
def P_D : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 : Matrix (Fin 8) (Fin 8) ℤ) - P_zero

/-- Algebraic trace readout against the displayed projector `P_zero`. -/
def katz_sarnak_trace (f : Matrix (Fin 8) (Fin 8) ℤ) : ℤ :=
  Matrix.trace (f * P_zero)

/-- The trace readout of the complementary displayed projector vanishes. -/
theorem projector_trace_vanishes_on_complement :
    katz_sarnak_trace P_D = 0 := by
  dsimp [katz_sarnak_trace, P_zero, P_D]
  decide

end InfoGeometry.Canonical.KatzSarnakDensity
