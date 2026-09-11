import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorBraidSigmaTransport
import InfoGeometry.Topology.ChiralOperatorBraidLatentFlow
import InfoGeometry.Topology.ChiralOperatorZornTopologicalMultiplication

/-!
# Equivariance of topological operator-valued Zorn multiplication

The cyclic colour action is an external operator action.  This owner proves
that it is compatible with the transported Zorn multiplication on the finite
product carrier, using the already established dot/cross transport laws.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

theorem chiralOperatorCycle_zornMul_equivariant
    (X Y : OperatorSageTopologicalCarrier A) :
    chiralOperatorCycle (operatorSageTopologicalMul X Y) =
      operatorSageTopologicalMul (chiralOperatorCycle X)
        (chiralOperatorCycle Y) := by
  rcases X with ⟨xPlus, xMinus, xSigmaPlus, xSigmaMinus⟩
  rcases Y with ⟨yPlus, yMinus, ySigmaPlus, ySigmaMinus⟩
  apply Prod.ext
  · simp [chiralOperatorCycle, operatorSageTopologicalMul,
      operatorCycle_dot]
  apply Prod.ext
  · simp [chiralOperatorCycle, operatorSageTopologicalMul,
      operatorCycle_dot]
  apply Prod.ext
  · funext c
    simp only [chiralOperatorCycle, operatorSageTopologicalMul,
      operatorCycleVec_apply]
    congr 1
    exact congrFun (operatorCycle_cross xSigmaMinus ySigmaMinus) c
  · funext c
    simp only [chiralOperatorCycle, operatorSageTopologicalMul,
      operatorCycleVec_apply]
    congr 1
    exact congrFun (operatorCycle_cross xSigmaPlus ySigmaPlus) c

theorem continuous_chiralOperatorCycle_zornMul_equivariant_readout
    (X Y : OperatorSageTopologicalCarrier A) :
    operatorSageObservationMap
        (chiralOperatorCycle (operatorSageTopologicalMul X Y)) =
      operatorSageObservationMap
        (operatorSageTopologicalMul (chiralOperatorCycle X)
          (chiralOperatorCycle Y)) := by
  rw [chiralOperatorCycle_zornMul_equivariant]

end
end InfoGeometry.Topology
