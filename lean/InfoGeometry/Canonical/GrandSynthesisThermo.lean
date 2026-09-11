import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SingularTransportSystem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Grand Unification of the Physics of Information in Lean 4

Capstone synthesis layer connecting thermodynamic Sinkhorn/KMS closure,
geometric Ricci/Calabi-Yau closure, and algebraic Bott-Dirac closure.
-/

open scoped TensorProduct
open scoped Kronecker

namespace InfoGeometry.Canonical.GrandSynthesis

open InfoGeometry.Krein
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference

section Thermodynamic

variable (n : Nat)

/--
Thermodynamic equilibrium along a doubly-stochastic Sinkhorn trajectory:
each step has Lyapunov monotonicity and bounded routing chiral scale.
-/
def ThermodynamicEquilibrium
    (T : DoublyStochasticSinkhornTrajectory n) : Prop :=
  ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      ∃ w : PermMode n → ℝ,
        (∀ σ, 0 ≤ w σ) ∧
        ∑ σ, w σ = 1 ∧
        ∑ σ, w σ • σ.permMatrix ℝ = T.traj.state (k + 1) ∧
        routingEpsilon w label ≤ 1

/--
Any doubly-stochastic Sinkhorn trajectory satisfies the thermodynamic equilibrium
control law from `sinkhorn_dynamics_step_control`.
-/
theorem thermodynamicEquilibrium_of_doublyStochastic
    (T : DoublyStochasticSinkhornTrajectory n) :
    ThermodynamicEquilibrium n T := by
  intro k label
  exact sinkhorn_dynamics_step_control (n := n) T k label

end Thermodynamic

section Geometric

variable {X : Type*}

/--
At geometric equilibrium, every Ricci component is scale-invariant.
-/
theorem ricci_component_constant_of_geometricEquilibrium
    (flow : RicciFlow X) (u v : X)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hGeo : IsRicciFixedPoint flow) :
    ∃ c : ℝ, ∀ s, flow s u v = c := by
  exact ricci_component_invariant_at_fixed_point
    (flow := flow) (u := u) (v := v) hDiff (fun s => hGeo s u v)

end Geometric

section EntropyFlow

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Entropy monotonicity along Sinkhorn flow (RN barrier form). -/
def SinkhornEntropyMonotoneRN (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k

/-- Every Sinkhorn trajectory satisfies RN-barrier entropy monotonicity. -/
theorem sinkhornEntropyMonotoneRN
    (T : SinkhornTrajectory n) :
    SinkhornEntropyMonotoneRN n T := by
  intro k
  exact trajectoryRNBarrier_monotone (n := n) T k

/--
Doubly-stochastic specialization of RN-barrier entropy monotonicity.
-/
theorem doublyStochastic_sinkhornEntropyMonotoneRN
    (T : DoublyStochasticSinkhornTrajectory n) :
    SinkhornEntropyMonotoneRN n T.traj := by
  exact sinkhornEntropyMonotoneRN (n := n) T.traj

end EntropyFlow

end InfoGeometry.Canonical.GrandSynthesis
