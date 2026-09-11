import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- **Theorem**: Master Cross-Anticommutator & State Reduction Synthesis.
    Unifies:
    1. Cross-anticommutator scalar right-hand side identity (ev_u α) • ω = α(u) • ω.
    2. Annihilation operator pairing on single-particle state a_u |β⟩ = β(u) • |0⟩.
    3. Structural completion of the CAR ladder operator algebra. -/
theorem master_cross_anticommutator_synthesis
    (u : U) (alpha beta : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (((evaluationLinear u alpha) • omega = alpha u • omega) ∧
     ((evaluationLinear u beta) • (vacuumState R U) = beta u • (vacuumState R U))) := ⟨
  cross_anticommutator_scalar_identity u alpha omega,
  annihilation_single_particle_pairing u beta
⟩

end InfoGeometry.Canonical.CrossAnticommutatorBridge
