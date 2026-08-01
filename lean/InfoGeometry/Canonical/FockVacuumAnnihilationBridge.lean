import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.FockVacuumAnnihilationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Fock Space Vacuum State |0⟩ = 1 ∈ ExteriorAlgebra R (U →ₗ[R] R). -/
def vacuumState (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] : ExteriorAlgebra R (U →ₗ[R] R) :=
  1

/-- **Theorem**: Annihilation Operator Annihilates Vacuum State (a_u |0⟩ = 0). -/
theorem annihilation_vacuum_zero (u : U) :
    (contractionOp (evaluationLinear u)) (vacuumState R U) = 0 := by
  dsimp [vacuumState, contractionOp]

end InfoGeometry.Canonical.FockVacuumAnnihilationBridge
