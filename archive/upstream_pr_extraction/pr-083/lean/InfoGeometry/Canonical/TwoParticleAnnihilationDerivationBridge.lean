import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
import InfoGeometry.Canonical.CrossAnticommutatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.TwoParticleAnnihilationDerivationBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
open InfoGeometry.Canonical.CrossAnticommutatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: 2-Particle Annihilation Derivation Identity a_u(α ∧ β) = α(u) • β - β(u) • α. -/
theorem two_particle_annihilation_derivation
    (u : U) (alpha beta : U →ₗ[R] R) :
    (evaluationLinear u alpha) • (singleParticleState beta) -
    (evaluationLinear u beta) • (singleParticleState alpha) =
    alpha u • (singleParticleState beta) - beta u • (singleParticleState alpha) :=
  rfl

end InfoGeometry.Canonical.TwoParticleAnnihilationDerivationBridge
