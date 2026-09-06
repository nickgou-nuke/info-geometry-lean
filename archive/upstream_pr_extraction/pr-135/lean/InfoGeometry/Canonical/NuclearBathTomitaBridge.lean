import InfoGeometry.Canonical.NuclearBathCommutant
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics

noncomputable section

namespace InfoGeometry.Canonical.NuclearBathTomitaBridge

open InfoGeometry.Canonical.NuclearBathCommutant
open InfoGeometry.Canonical.SL2SpinorLadder
open InfoGeometry.OperatorAlgebra.Thermodynamics

abbrev AdjointTomitaKMSDatum :=
  TomitaKMSDatum AdjointOperator

/-! The existing Tomita/KMS contract is applied to the associative operator
image of the native nuclear Lie carrier.  No new state or flow is introduced. -/

theorem adjoint_observable_modular_invariant
    (T : AdjointTomitaKMSDatum)
    (t : ℝ) (X : Alg) :
    T.state.eval (T.modularFlow.flow t (adjointOperator X)) =
      T.state.eval (adjointOperator X) := by
  exact T.modular_invariant t (adjointOperator X)

theorem adjoint_observable_kms_boundary
    (T : AdjointTomitaKMSDatum) :
    T.toKMSState.kms.boundaryCondition := by
  exact T.toKMSState_is_KMS

end InfoGeometry.Canonical.NuclearBathTomitaBridge
