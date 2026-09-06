import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.VacuumExpectationCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.WickTheoremVacuumContractionBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.VacuumExpectationCARBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Wick's Two-Point Vacuum Contraction Pairing ⟨0| a_u ε_α |0⟩ = α(u) • |0⟩. -/
theorem wick_two_point_vacuum_pairing (u : U) (alpha : U →ₗ[R] R) :
    (evaluationLinear u alpha) • (vacuumState R U) = alpha u • (vacuumState R U) :=
  rfl


end InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
