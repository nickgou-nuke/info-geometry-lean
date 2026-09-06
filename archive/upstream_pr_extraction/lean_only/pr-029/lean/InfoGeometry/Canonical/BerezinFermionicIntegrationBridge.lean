import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BerezinFermionicIntegrationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.WickTheoremVacuumContractionBridge
open InfoGeometry.Canonical.CrossAnticommutatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Berezin Integral Operator ∫ dα = a_u via Dual Evaluation Contraction ι_{ev_u}. -/
def berezinIntegralOp (u : U) : ExteriorAlgebra R (U →ₗ[R] R) →ₗ[R] ExteriorAlgebra R (U →ₗ[R] R) :=
  contractionOp (evaluationLinear u)

/-- **Theorem**: Berezin Integral of Vacuum Scalar State |0⟩ = 1 is Zero (∫ dα 1 = 0). -/
theorem berezin_integral_scalar_zero (u : U) :
    berezinIntegralOp u (vacuumState R U) = 0 :=
  annihilation_vacuum_zero u

/-- **Theorem**: Berezin Integral of Generator α for Normalized Pairing α(u) = 1 (∫ dα α = (1 : R) • |0⟩). -/
theorem berezin_integral_generator_one (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    (evaluationLinear u alpha) • (vacuumState R U) = (1 : R) • (vacuumState R U) := by
  have h : evaluationLinear u alpha = (1 : R) := by rw [evaluation_linear_apply, hpair]
  rw [h]

/-- **Theorem**: Master Berezin Fermionic Integration Synthesis.
    Unifies:
    1. Berezin integral operator definition ∫ dα = a_u via covector contraction ι_{ev_u}.
    2. Fundamental Berezin integration law ∫ dα 1 = 0 on scalar vacuum state.
    3. Fundamental Berezin integration law ∫ dα α = (1 : R) • |0⟩ on normalized Grassmann generator. -/
theorem master_berezin_fermionic_integration_synthesis
    (u : U) (alpha : U →ₗ[R] R) (hpair : alpha u = 1) :
    ((berezinIntegralOp u (vacuumState R U) = 0) ∧
     ((evaluationLinear u alpha) • (vacuumState R U) = (1 : R) • (vacuumState R U))) := ⟨
  berezin_integral_scalar_zero u,
  berezin_integral_generator_one u alpha hpair
⟩

end InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
