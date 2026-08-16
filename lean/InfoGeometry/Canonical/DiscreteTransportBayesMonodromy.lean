import InfoGeometry.Canonical.OperatorJKOStep
import InfoGeometry.Canonical.MajoranaJKOErgoBridge
import InfoGeometry.Dynamics.JkoWeylGromov
import InfoGeometry.OptimalTransport.EntropyGradientFlow
import InfoGeometry.Quantum.Monodromy
import InfoGeometry.Quantum.RealKCategory

/-!
# InfoGeometry.Canonical.DiscreteTransportBayesMonodromy

Thin bridge packet for the discrete transport / JKO / Bayesian evolution lane.

This file does not create new analytic theory. It exposes, in one place, the
already-owned finite readouts that property the repo's discrete transport story:

- deterministic JKO energy decay;
- Bayesian update equals the selected JKO next state;
- Bregman/JKO projection identity;
- finite quadratic transport energy decrease;
- Bregman/monodromy finite-step collapse;
- square-zero Jordan power law.

This is the formal packet corresponding to the finite property surface used in
the SymPy scripts.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiscreteTransportBayesMonodromy

open InfoGeometry.Canonical.OperatorJKOStep
open InfoGeometry.Canonical.MajoranaJKOErgoBridge
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Quantum

section OperatorJKO

variable {Weight : Type*}
variable {P : OperatorJKOPotential Weight}

/-- Alias for the deterministic JKO energy-drop theorem. -/
theorem operatorJKO_energy_next_le_previous_energy
    (A : OperatorJKOArgmin P) :
    P.energy A.next ≤ P.energy A.previous := by
  exact A.energy_next_le_previous_energy

/-- Alias for the deterministic JKO transport-penalty bound. -/
theorem operatorJKO_penalty_le_energy_drop
    (A : OperatorJKOArgmin P) :
    P.penalty A.stepSize A.next A.previous ≤
      P.energy A.previous - P.energy A.next := by
  exact A.penalty_le_energy_drop

/-- Alias for the Bayesian calibration update equals the JKO next state. -/
theorem bayesUpdate_previous_eq_next_bridge
    {Weight Evidence : Type*}
    {P : OperatorJKOPotential Weight}
    (B : JKOBayesianCalibration (Weight := Weight) (Evidence := Evidence) P) :
    ∀ prior evidence, B.bayesUpdate prior evidence = (B.jkoStep prior evidence).next := by
  intro prior evidence
  exact B.bayes_eq_jko_next prior evidence

/-- Alias for the Bayesian/JKO Pythagorean projection identity. -/
theorem bayesian_projection_identity_bridge
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {State LieGroup LieAlgebra LieDual Observable : Type*}
    [AddMonoid LieAlgebra]
    [NormedRing Observable] [NormedAlgebra ℝ Observable] [CompleteSpace Observable]
    (B : MajoranaJKOErgoBridge (E := E) State LieGroup LieAlgebra LieDual Observable)
    (ρ : Density State)
    (hρ : B.feasibleAlternative ρ) :
    B.encodedDivergence ρ B.jko.previous =
      B.encodedDivergence ρ B.jko.next +
        B.encodedDivergence B.jko.next B.jko.previous := by
  exact B.bayesian_projection_identity ρ hρ

end OperatorJKO

section FiniteDynamics

/-- Alias for the finite quadratic JKO/Bayesian gradient energy decrease. -/
theorem quadraticJKO_free_energy_decrease
    (a : ℝ) (ha : a > 0)
    (x : ℝ) (hx : x ≠ 0)
    (τ : ℝ) (hτ1 : 0 < τ) (hτ2 : τ < 2 / a) :
    (1 / 2 : ℝ) * a * ((1 - τ * a) * x)^2 <
      (1 / 2 : ℝ) * a * x^2 := by
  exact InfoGeometry.Dynamics.free_energy_decrease a ha x hx τ hτ1 hτ2

/-- Alias for the finite Bregman/JKO proximal composition law. -/
theorem bregman_prox_induction
    (δ : ℂ) (n : ℕ) :
    InfoGeometry.OptimalTransport.EntropyGradientFlow.bregmanProxStep δ ^ n =
      InfoGeometry.OptimalTransport.EntropyGradientFlow.bregmanProxStep ((n : ℂ) * δ) := by
  exact InfoGeometry.OptimalTransport.EntropyGradientFlow.bregman_prox_induction δ n

/-- Alias for the monodromy-as-Bregman optimizer readout. -/
theorem monodromy_is_bregman_optimizer
    (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy h ^ n =
      InfoGeometry.Clifford.LogCftMonodromy.lcftPhase h ^ n •
        InfoGeometry.OptimalTransport.EntropyGradientFlow.bregmanProxStep
          ((n : ℂ) * InfoGeometry.Clifford.LogCftMonodromy.logShearBase) := by
  exact InfoGeometry.OptimalTransport.EntropyGradientFlow.monodromy_is_bregman_optimizer h n

/-- Alias for the square-zero Jordan power law. -/
theorem nilpotent_jordan_power
    {A : Type*} [Ring A]
    (u N : A) (h_comm : Commute u N) (h_nil : N * N = 0) (n : ℕ) :
    (u + N) ^ (n + 1) = u ^ (n + 1) + (n + 1) • (u ^ n * N) := by
  exact InfoGeometry.QuantumMonodromy.nilpotent_jordan_power u N h_comm h_nil n

end FiniteDynamics

end InfoGeometry.Canonical.DiscreteTransportBayesMonodromy
