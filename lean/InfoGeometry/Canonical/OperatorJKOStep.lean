/-
InfoGeometry/Canonical/OperatorJKOStep.lean

Deterministic operator JKO step backbone.

This module records a proof-carrying variational JKO update:

* an energy functional;
* a nonnegative transport/regularization penalty;
* an objective `energy(next) + penalty(next, previous)`;
* an explicit argmin witness.

It proves only the deterministic consequences of the installed minimizer:
energy decay, penalty control by energy drop, and objective control by the
previous state's energy.

It does not prove automatic argmin existence, weak compactness, uniqueness,
continuous-time convergence, stochastic dynamics, or Hudson-Parthasarathy
calculus.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.OperatorJKOStep

/-! ## 1. Operator JKO potential -/

/--
Operator JKO potential.

`energy` is the Lyapunov/free-energy readout.
`penalty τ next previous` is the transport or regularization cost for a time
step `τ`, moving from `previous` to `next`.
-/
structure OperatorJKOPotential
    (Weight : Type*) where
  /-- Energy/free-energy readout. -/
  energy :
    Weight → ℝ

  /-- Transport/regularization penalty. -/
  penalty :
    ℝ → Weight → Weight → ℝ

  /-- Penalties are nonnegative. -/
  penalty_nonneg :
    ∀ τ next previous,
      0 ≤ penalty τ next previous

  /-- Staying at the same state has zero penalty. -/
  penalty_self_eq_zero :
    ∀ τ previous,
      penalty τ previous previous = 0

namespace OperatorJKOPotential

variable {Weight : Type*}

variable (P : OperatorJKOPotential Weight)

/-- Deterministic JKO objective for a candidate `next` state. -/
def objective
    (τ : ℝ)
    (previous next : Weight) : ℝ :=
  P.energy next + P.penalty τ next previous

@[simp]
theorem objective_previous
    (τ : ℝ)
    (previous : Weight) :
    P.objective τ previous previous = P.energy previous := by
  simp [objective, P.penalty_self_eq_zero]

end OperatorJKOPotential

/-! ## 2. Argmin witness -/

/--
Proof-carrying deterministic JKO argmin.

The `minimizing` field is the only variational hypothesis. This structure does
not assert that minimizers exist automatically.
-/
structure OperatorJKOArgmin
    {Weight : Type*}
    (P : OperatorJKOPotential Weight) where
  /-- Previous/prior state. -/
  previous :
    Weight

  /-- Selected next/posterior state. -/
  next :
    Weight

  /-- Time step. -/
  stepSize :
    ℝ

  /-- Nonnegative time step. -/
  stepSize_nonneg :
    0 ≤ stepSize

  /-- The selected next state minimizes the installed objective. -/
  minimizing :
    ∀ candidate : Weight,
      P.objective stepSize previous next ≤
        P.objective stepSize previous candidate

namespace OperatorJKOArgmin

variable {Weight : Type*}
variable {P : OperatorJKOPotential Weight}

variable (A : OperatorJKOArgmin P)

/-- The selected next state has objective no larger than the previous state. -/
theorem objective_le_previous_energy :
    P.objective A.stepSize A.previous A.next ≤
      P.energy A.previous := by
  simpa using A.minimizing A.previous

/-- The JKO update decreases energy. -/
theorem energy_next_le_previous_energy :
    P.energy A.next ≤ P.energy A.previous := by
  have hobj : P.objective A.stepSize A.previous A.next ≤ P.energy A.previous :=
    A.objective_le_previous_energy
  have hpen : 0 ≤ P.penalty A.stepSize A.next A.previous :=
    P.penalty_nonneg A.stepSize A.next A.previous
  dsimp [OperatorJKOPotential.objective] at hobj
  linarith

/-- The transport penalty is bounded by the energy drop. -/
theorem penalty_le_energy_drop :
    P.penalty A.stepSize A.next A.previous ≤
      P.energy A.previous - P.energy A.next := by
  have hobj : P.objective A.stepSize A.previous A.next ≤ P.energy A.previous :=
    A.objective_le_previous_energy
  dsimp [OperatorJKOPotential.objective] at hobj
  linarith

end OperatorJKOArgmin

/-! ## 3. Argmin backend socket -/

/--
Backend socket for selecting deterministic JKO argmins.

This is a witness layer: a concrete compactness/convexity argument may fill it,
but no such existence theorem is proved here.
-/
structure OperatorJKOArgminBackend
    (Weight : Type*)
    (P : OperatorJKOPotential Weight) where
  /-- Select an argmin witness for a previous state and step size. -/
  select :
    Weight → ℝ → OperatorJKOArgmin P

  /-- The selected argmin has the requested previous state. -/
  selected_previous :
    ∀ previous τ,
      (select previous τ).previous = previous

  /-- The selected argmin has the requested step size. -/
  selected_stepSize :
    ∀ previous τ,
      (select previous τ).stepSize = τ

/-! ## 4. JKO paths -/

/--
Discrete deterministic JKO path.

The path stores a sequence of argmin witnesses rather than raw states, so every
step carries its own minimization certificate.
-/
structure OperatorJKOPath
    {Weight : Type*}
    (P : OperatorJKOPotential Weight) where
  /-- Argmin witness at each step. -/
  step :
    ℕ → OperatorJKOArgmin P

namespace OperatorJKOPath

variable {Weight : Type*}
variable {P : OperatorJKOPotential Weight}

variable (Γ : OperatorJKOPath P)

/-- Energy decreases at every stored JKO step. -/
theorem energy_antitone_step
    (n : ℕ) :
    P.energy (Γ.step n).next ≤ P.energy (Γ.step n).previous :=
  (Γ.step n).energy_next_le_previous_energy

/-- Penalty is bounded by energy drop at every stored JKO step. -/
theorem penalty_le_energy_drop_step
    (n : ℕ) :
    P.penalty (Γ.step n).stepSize (Γ.step n).next (Γ.step n).previous ≤
      P.energy (Γ.step n).previous - P.energy (Γ.step n).next :=
  (Γ.step n).penalty_le_energy_drop

end OperatorJKOPath

/-! ## 5. Bayesian calibration -/

/--
Bayesian calibration of a deterministic JKO step.

This states that a supplied Bayesian/update map selects the same `next` state
as a supplied deterministic JKO argmin witness.
-/
structure JKOBayesianCalibration
    {Weight Evidence : Type*}
    (potential : OperatorJKOPotential Weight) where
  /-- Bayesian/discrete update map. -/
  bayesUpdate :
    Weight → Evidence → Weight

  /-- Evidence-dependent step size. -/
  stepSize :
    Evidence → ℝ

  /-- Selected JKO argmin witness for each prior/evidence pair. -/
  jkoStep :
    Weight → Evidence → OperatorJKOArgmin potential

  /-- Bayesian posterior agrees with the selected JKO next state. -/
  bayes_eq_jko_next :
    ∀ prior evidence,
      bayesUpdate prior evidence = (jkoStep prior evidence).next

  /-- Selected JKO previous state is the prior. -/
  jko_previous :
    ∀ prior evidence,
      (jkoStep prior evidence).previous = prior

  /-- Selected JKO step size is the evidence-dependent step size. -/
  jko_stepSize :
    ∀ prior evidence,
      (jkoStep prior evidence).stepSize = stepSize evidence

namespace JKOBayesianCalibration

variable {Weight Evidence : Type*}
variable {P : OperatorJKOPotential Weight}

variable (B : JKOBayesianCalibration (Weight := Weight) (Evidence := Evidence) P)

/-- The Bayesian posterior inherits deterministic JKO energy decay. -/
theorem bayes_energy_le_prior_energy
    (prior : Weight)
    (evidence : Evidence) :
    P.energy (B.bayesUpdate prior evidence) ≤ P.energy prior := by
  calc
    P.energy (B.bayesUpdate prior evidence)
        = P.energy (B.jkoStep prior evidence).next := by
            rw [B.bayes_eq_jko_next prior evidence]
    _ ≤ P.energy (B.jkoStep prior evidence).previous :=
            (B.jkoStep prior evidence).energy_next_le_previous_energy
    _ = P.energy prior := by
            rw [B.jko_previous prior evidence]

/-- The selected Bayesian/JKO penalty is bounded by the energy drop. -/
theorem jko_penalty_le_energy_drop
    (prior : Weight)
    (evidence : Evidence) :
    P.penalty
        (B.jkoStep prior evidence).stepSize
        (B.jkoStep prior evidence).next
        (B.jkoStep prior evidence).previous
      ≤
    P.energy (B.jkoStep prior evidence).previous -
      P.energy (B.jkoStep prior evidence).next :=
  (B.jkoStep prior evidence).penalty_le_energy_drop

end JKOBayesianCalibration

/-! ## 6. Optional noisy and limit carriers -/

/--
Noisy JKO update carrier.

This records a noisy correction layer without introducing stochastic calculus.
No correction theorem is asserted at this generic level; concrete stochastic
models must state and prove their correction law in their owner module.
-/
structure NoisyJKOUpdate
    {Weight Noise : Type*}
    (P : OperatorJKOPotential Weight) where
  /-- Deterministic backbone step. -/
  deterministic :
    OperatorJKOArgmin P

  /-- Noise input. -/
  noise :
    Noise

  /-- Noisy/corrected next state. -/
  noisyNext :
    Weight

namespace NoisyJKOUpdate

variable {Weight Noise : Type*}
variable {P : OperatorJKOPotential Weight}

end NoisyJKOUpdate

/--
Modular/continuous-flow limit calibration carrier.

This does not prove `τ → 0` convergence. It records only the discrete path and
continuous/modular-flow readout.  Concrete analytic models must state and prove
their convergence theorem in their owner module.
-/
structure JKOModularFlowLimitCalibration
    {Weight FlowReadout : Type*}
    (P : OperatorJKOPotential Weight) where
  /-- Discrete JKO path. -/
  path :
    OperatorJKOPath P

  /-- Continuous/modular-flow readout. -/
  flowReadout :
    FlowReadout

namespace JKOModularFlowLimitCalibration

variable {Weight FlowReadout : Type*}
variable {P : OperatorJKOPotential Weight}

end JKOModularFlowLimitCalibration

end InfoGeometry.Canonical.OperatorJKOStep
