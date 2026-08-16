import Mathlib.Tactic
import InfoGeometry.Canonical.BayesianDiscreteHodgeBridge
import InfoGeometry.Canonical.BayesianHodgeCurrent
import InfoGeometry.Canonical.BayesianHodgeStabilizerBridge
import InfoGeometry.Canonical.BuresMetricStabilization
import InfoGeometry.Canonical.DiscreteDiracHodgeChiralBridge
import InfoGeometry.Canonical.InfinitesimalDictionaryBridge
import InfoGeometry.Canonical.MaximumCaliberKLSplit
import InfoGeometry.Canonical.MaximumCaliberPath
import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Bayesian / Thermodynamic / Bures / Hodge Integration Bridge

Theorem-safe integration layer tying together the finite bridge modules already
present in the repository.

This file does **not** assert a full continuum spacetime theorem. It records the
exact finite readback pattern showing how:

* antisymmetric divergence/current readouts calibrate to `d log Q`;
* coexact MaxCal currents realize the nonequilibrium/entropy lane;
* harmonic Bayesian posteriors land in the stabilizer-protected kernel; and
* equal local states have zero limit Bures cost.
-/

namespace InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge

open InfinitesimalDictionaryBridge
open BayesianDiscreteHodgeBridge
open BayesianHodgeCurrent
open BayesianHodgeStabilizerBridge
open BuresMetricStabilization
open MaximumCaliberKLSplit
open MaximumCaliberPath
open DiscreteDiracHodgeChiralBridge
open TensorColimitExpectation
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Topology.DiscreteHodgeStabilizer

universe u v w

section ScalarCurrentCalibration

variable {Θ V State Op Alg X : Type*}
variable [AddCommGroup V] [AddGroup Op] [Ring Alg]
variable (P : InfinitesimalDictionaryModel Θ V State Op Alg X)

/--
If the antisymmetric divergence is calibrated to the packet's scalar current
readout and that scalar current readout is itself chosen as the `d log Q`
readout, then the antisymmetric divergence is the scalar `d log Q` current.
-/
theorem antisymmetric_eq_scalar_dlnQ_of_calibration
    (ω φ : State)
    (hcal :
      antisymmetricDivergence P.divergence ω φ = P.pathConstraintScalar) :
    antisymmetricDivergence P.divergence ω φ = P.pathReadout P.gauge.flow.d_ln_Q := by
  rw [hcal, P.pathConstraintScalar_eq_dlnQ_readout]

end ScalarCurrentCalibration

section HodgeProtection

variable {n0 n1 n2 : ℕ}

/--
A Bayesian-updated harmonic current is protected from exact and coexact local
error sectors.
-/
theorem posterior_harmonic_protected
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    eckmannDot posterior exactErr = 0 ∧ eckmannDot posterior coexactErr = 0 := by
  rcases bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact with
    ⟨_, _, _, _, hExact, hCoexact⟩
  exact ⟨hExact, hCoexact⟩

/-- A protected harmonic `K₃` packet has zero carrier when both closed and coclosed. -/
theorem K3_harmonic_packet_zero
    (P : K3HodgeModePacket) :
    P.ω = 0 :=
  P.harmonic_eq_zero

end HodgeProtection

section BuresReadout

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]
variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable {L : TensorInductiveLimit (R := R) (A := A) bond}
variable (B : BuresMetricStabilizationBridge L)

/--
If the tracked local pair of states agrees at stage `n`, then the integrated
limit metric readout vanishes at that stage.
-/
theorem zero_limit_metric_of_equal_local_states
    (n : ℕ)
    (hEq : B.rho n = B.sigma n) :
    B.BWInf.squaredDist (B.toLimitState n (B.rho n)) (B.toLimitState n (B.sigma n)) = 0 :=
  B.bures_cost_limit_eq_zero_of_stage_eq n hEq

end BuresReadout

section CoexactCurrent

variable {n0 n1 n2 : ℕ}

/--
The calibrated coexact current reads out the logarithmic de Rham current.
-/
theorem coexact_current_eq_dlnQ
    (B : CoexactMaxCalCurrentReadout (n0 := n0) (n1 := n1) (n2 := n2)) :
    B.currentReadout B.current = B.flow.d_ln_Q :=
  B.currentReadout_eq_dlnQ

end CoexactCurrent

end InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge
