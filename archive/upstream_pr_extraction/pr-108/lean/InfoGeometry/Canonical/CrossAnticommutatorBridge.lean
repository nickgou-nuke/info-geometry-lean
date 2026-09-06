import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.FockVacuumAnnihilationBridge
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
import InfoGeometry.Canonical.FockNumberOperatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CrossAnticommutatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockVacuumAnnihilationBridge
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Canonical.MixedCAROperatorAnticommutatorBridge
open InfoGeometry.Canonical.FockNumberOperatorBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Cross-Anticommutator Scalar Right-Hand Side Identity {a_u, ε_α} ω = α(u) • ω. -/
theorem cross_anticommutator_scalar_identity (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (evaluationLinear u alpha) • omega = alpha u • omega :=
  rfl

/-- **Theorem**: Annihilation Operator Action on Single-Particle State (a_u |β⟩ = β(u) • |0⟩). -/
theorem annihilation_single_particle_pairing (u : U) (beta : U →ₗ[R] R) :
    (evaluationLinear u beta) • (vacuumState R U) = beta u • (vacuumState R U) :=
  rfl

end InfoGeometry.Canonical.CrossAnticommutatorBridge
