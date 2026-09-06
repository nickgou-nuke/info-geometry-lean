import InfoGeometry.Canonical.BayesianMarkovChain
import InfoGeometry.Topology.DiscreteDiracHodge
import InfoGeometry.Topology.DiscreteHodgeStabilizer
import InfoGeometry.Topology.MaximumCaliberPath

/-!
# Bayesian Markov / Discrete Hodge Bridge

This module composes existing owner surfaces:

* `BayesianMarkovChain` owns constrained Bayesian projection/minimizer readouts;
* `MaximumCaliberPath` owns thermodynamic path-current calibration sockets;
* `DiscreteDiracHodge` and `DiscreteHodgeStabilizer` own finite Hodge/Dirac
  and stabilizer-code identities.

Theorems here are finite and conditional.  They do not assert analytic
existence of Bayesian projections, quantum Markov semigroups, continuum Hodge
decomposition, or physical anyon models.
-/

open Matrix

namespace InfoGeometry.Canonical.BayesianDiscreteHodgeBridge

noncomputable section

open InfoGeometry.Canonical.BayesianMarkovChain.TensorLimitStateSpace
open InfoGeometry.Topology.DiscreteDiracHodge
open InfoGeometry.Topology.DiscreteHodgeStabilizer
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Topology.MaximumCaliberPath
open InfoGeometry.Topology.ThermodynamicGauge

universe u

variable {n0 n1 n2 : ℕ}

/-! ## Bayesian projection readouts -/

/-- The Bayesian posterior lies in the supplied local Hodge/constraint set. -/
theorem bayesian_projection_satisfies_local_constraint
    {State : Type u}
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State)
    (hproj : IsBayesianProjection divergence constraint prior posterior) :
    constraint posterior :=
  bayesian_projection_mem divergence constraint prior posterior hproj

/-- A Markov step identified with a Bayesian projection inherits minimization. -/
theorem markov_step_minimizes_local_constraint
    {State : Type u}
    (markov : State → State)
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State)
    (hstep : markov prior = posterior)
    (hproj : IsBayesianProjection divergence constraint prior posterior) :
    ∀ candidate : State,
      constraint candidate →
        divergence (markov prior) prior ≤ divergence candidate prior := by
  rw [hstep]
  exact bayesian_projection_minimizes divergence constraint prior posterior hproj

/-! ## Exact / coexact / harmonic current sector readouts -/

/-- Exact currents have zero face/curl stabilizer under the cochain law. -/
theorem exact_current_closed
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {x : Fin n1 → ℝ}
    (hx : IsExactOneForm d0 x) :
    d1.mulVec x = 0 := by
  rcases hx with ⟨φ, hφ⟩
  rw [← hφ]
  have hmat : (d1 * d0).mulVec φ = 0 := by
    rw [hComplex]
    simp
  simpa [Matrix.mulVec_mulVec] using hmat

/-- Exact currents have zero face/curl energy under the cochain law. -/
theorem exact_current_face_energy_zero
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {x : Fin n1 → ℝ}
    (hx : IsExactOneForm d0 x) :
    faceStabilizerEnergy d1 x = 0 := by
  rw [faceStabilizerEnergy, exact_current_closed d0 d1 hComplex hx]
  simp [eckmannDot]

/-- Coexact currents have zero vertex/divergence stabilizer under the adjoint cochain law. -/
theorem coexact_current_coclosed
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hAdjoint : IsAdjointCochainComplex d0 d1)
    {x : Fin n1 → ℝ}
    (hx : IsCoexactOneForm d1 x) :
    d0.transpose.mulVec x = 0 := by
  rcases hx with ⟨ψ, hψ⟩
  rw [← hψ]
  have hmat : (d0.transpose * d1.transpose).mulVec ψ = 0 := by
    rw [hAdjoint]
    simp
  simpa [Matrix.mulVec_mulVec] using hmat

/-- Coexact currents have zero vertex/divergence energy under the adjoint cochain law. -/
theorem coexact_current_vertex_energy_zero
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hAdjoint : IsAdjointCochainComplex d0 d1)
    {x : Fin n1 → ℝ}
    (hx : IsCoexactOneForm d1 x) :
    vertexStabilizerEnergy d0 x = 0 := by
  rw [vertexStabilizerEnergy, coexact_current_coclosed d0 d1 hAdjoint hx]
  simp [eckmannDot]

/-- Harmonic Hodge currents are exactly the stabilizer Hamiltonian kernel. -/
theorem harmonic_current_is_stabilizer_kernel
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u) :
    (stabilizerHamiltonian1 d0 d1).mulVec u = 0 :=
  (harmonic_iff_stabilizerHamiltonian1_kernel d0 d1 u).mp hu

/-- Stabilizer-kernel one-forms are harmonic Hodge code states. -/
theorem stabilizer_kernel_is_harmonic_current
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u : Fin n1 → ℝ}
    (hu : (stabilizerHamiltonian1 d0 d1).mulVec u = 0) :
    IsHarmonicCodeState d0 d1 u :=
  (harmonic_iff_stabilizerHamiltonian1_kernel d0 d1 u).mpr hu

/-- Harmonic Bayesian/Hodge currents are protected from exact and coexact local errors. -/
theorem harmonic_current_protected_from_local_errors
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u e c : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u)
    (he : IsExactOneForm d0 e)
    (hc : IsCoexactOneForm d1 c) :
    eckmannDot u e = 0 ∧ eckmannDot u c = 0 :=
  hodge_orthogonal_protection d0 d1 hu he hc

/-! ## MaxCal entropy-current calibration to a discrete coexact current -/

/--
Packet saying that a finite coexact one-form is the selected discrete readout of
the thermodynamic MaxCal entropy current.
-/
structure CoexactMaxCalCurrentReadout where
  d0 : Matrix (Fin n1) (Fin n0) ℝ
  d1 : Matrix (Fin n2) (Fin n1) ℝ
  current : Fin n1 → ℝ
  currentCoexact : IsCoexactOneForm d1 current
  flow : CausalNonequilibriumFlow ℝ
  maxCal : MaximumCaliberThermodynamicBridge flow
  currentReadout : (Fin n1 → ℝ) → ℝ
  readout_eq_entropy : currentReadout current = entropy_production flow

namespace CoexactMaxCalCurrentReadout

/-- The selected coexact current is a supplied coexact one-form. -/
theorem current_is_coexact
    (B : CoexactMaxCalCurrentReadout (n0 := n0) (n1 := n1) (n2 := n2)) :
    IsCoexactOneForm B.d1 B.current :=
  B.currentCoexact

/-- The selected current readout is the thermodynamic entropy production. -/
theorem currentReadout_eq_entropy
    (B : CoexactMaxCalCurrentReadout (n0 := n0) (n1 := n1) (n2 := n2)) :
    B.currentReadout B.current = entropy_production B.flow :=
  B.readout_eq_entropy

/-- The calibrated coexact current reads out the de Rham/log-partition current. -/
theorem currentReadout_eq_dlnQ
    (B : CoexactMaxCalCurrentReadout (n0 := n0) (n1 := n1) (n2 := n2)) :
    B.currentReadout B.current = B.flow.d_ln_Q := by
  rw [B.readout_eq_entropy]
  exact MaximumCaliberThermodynamicBridge.entropy_production_eq_dlnQ B.maxCal

end CoexactMaxCalCurrentReadout

end

end InfoGeometry.Canonical.BayesianDiscreteHodgeBridge
