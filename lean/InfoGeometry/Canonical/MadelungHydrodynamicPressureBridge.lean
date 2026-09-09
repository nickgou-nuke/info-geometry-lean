import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset

namespace MadelungHydrodynamic

/-- Madelung Quantum Fluid State on a discrete spatial lattice. -/
structure MadelungState (n : Type*) [Fintype n] [DecidableEq n] where
  rho : n → ℝ             -- Fluid density ρ(x)
  rho_pos : ∀ i, 0 < rho i
  gradS : n → ℝ           -- Gradient of action phase ∇S(x)
  mass : ℝ
  mass_pos : 0 < mass

namespace MadelungState

variable {n : Type*} [Fintype n] [DecidableEq n] (state : MadelungState n)

/-- Madelung hydrodynamical velocity field v_i = (1 / m) * ∇S_i -/
def velocity (i : n) : ℝ :=
  (1 / state.mass) * state.gradS i

/-- **Theorem**: Velocity is proportional to action phase gradient. -/
theorem velocity_prop_gradS (i : n) :
    state.velocity i * state.mass = state.gradS i := by
  dsimp [velocity]
  have hm : state.mass ≠ 0 := ne_of_gt state.mass_pos
  calc (1 / state.mass) * state.gradS i * state.mass
    _ = ((1 / state.mass) * state.mass) * state.gradS i := by ring
    _ = 1 * state.gradS i := by rw [one_div_mul_cancel hm]
    _ = state.gradS i := by ring

/-- Quantum Information Potential Q_i defined from Fisher-Rao amplitude curvature. -/
def quantumPotential (laplacian_sqrt_rho : n → ℝ) (hbar : ℝ) (i : n) : ℝ :=
  - ((hbar ^ 2) / (2 * state.mass)) * (laplacian_sqrt_rho i / Real.sqrt (state.rho i))

/-- **Theorem**: Quantum potential vanishes for uniform density field (laplacian = 0). -/
theorem quantum_potential_zero_uniform (hbar : ℝ) (i : n) :
    state.quantumPotential (fun _ => 0) hbar i = 0 := by
  dsimp [quantumPotential]
  ring

/-- Quantum Information Pressure Gradient F_quantum = -∇ Q_quantum. -/
def informationPressureGradient (gradQ : n → ℝ) (i : n) : ℝ :=
  - gradQ i

/-- **Theorem**: Vanishing quantum potential gradient yields zero quantum force: ∇Q = 0 ⟹ F_quantum = 0. -/
theorem info_pressure_zero (i : n) :
    informationPressureGradient (fun _ => 0) i = 0 := by
  dsimp [informationPressureGradient]
  ring

end MadelungState

end MadelungHydrodynamic
