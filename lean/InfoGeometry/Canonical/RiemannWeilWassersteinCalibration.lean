import Mathlib
import InfoGeometry.Meta.CalibrationReexport
import InfoGeometry.Canonical.HamiltonianFlowBridge

/-!
# InfoGeometry.Canonical.RiemannWeilWassersteinCalibration

Canonical wrapper for the existing Riemann--Weil/Wasserstein bridge theorem.

This file adds no new analytic content. It re-exports the already-native
`riemann_weil_wasserstein_identification` theorem under a canonical owner-facing
namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.RiemannWeilWassersteinCalibration

open InfoGeometry.Canonical
open InfoGeometry.Canonical.HamiltonianFlowBridge
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Convex
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E

/--
Canonical re-export of the Riemann--Weil/Wasserstein identification.
-/
theorem riemann_weil_wasserstein_force_readout
    (F : GrandCanonicalHamiltonianFlowBridge (E := E))
    (Ex : ExplicitFormulaVectorField H₂)
    (hEquiv : F.engine.logPartitionDerivative = Ex.logEulerDerivative)
    (hExplicitConsistency :
      ∀ x : H₂, Ex.wassersteinField x = Ex.explicitFormula (F.stateToScale x)) :
    ∀ x : H₂, F.forceField.thermodynamicForce x = Ex.wassersteinField x := by
  reexport riemann_weil_wasserstein_identification F Ex hEquiv hExplicitConsistency

end InfoGeometry.Canonical.RiemannWeilWassersteinCalibration
