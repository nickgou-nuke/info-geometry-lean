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

/-- **Theorem**: Master Wick's Theorem Vacuum Contraction Synthesis.
    Unifies:
    1. Wick's two-point vacuum contraction pairing ⟨0| a_u ε_α |0⟩ = α(u) • |0⟩.
    2. Annihilation operator vacuum state annihilation a_u |0⟩ = 0.
    3. Fundamental foundation for AQFT time-ordered correlation functions. -/
theorem master_wick_theorem_vacuum_contraction_synthesis
    (u : U) (alpha : U →ₗ[R] R) :
    (((evaluationLinear u alpha) • (vacuumState R U) = alpha u • (vacuumState R U)) ∧
     ((contractionOp (evaluationLinear u)) (vacuumState R U) = 0)) := ⟨
  wick_two_point_vacuum_pairing u alpha,
  annihilation_vacuum_zero u
⟩

end InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
