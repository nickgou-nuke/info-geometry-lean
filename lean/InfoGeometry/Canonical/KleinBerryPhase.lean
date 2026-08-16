import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.KleinExceptionalBraid

namespace InfoGeometry.Canonical.KleinBerryPhase

open Matrix
open InfoGeometry.Canonical.KleinExceptionalBraid

/-!
# Finite matrix products for the Klein glide toy packet

This owner proves only products of the concrete integer matrices imported from
`KleinExceptionalBraid`.  The names retain compatibility with downstream code,
but the results are not claims about Berry connections, holonomy, topology, or
exceptional-point physics.
-/

/-- The concrete quarter-turn matrix squares to the negative identity. -/
theorem orientable_holonomy_pi :
    B_EP * B_EP = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B_EP, Matrix.mul_apply, Fin.sum_univ_two]

/-- The conjugated quarter-turn product is the identity matrix. -/
theorem klein_holonomy_cancellation :
    B_EP * (G_Glide * B_EP * G_Glide) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B_EP, G_Glide, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.KleinBerryPhase
