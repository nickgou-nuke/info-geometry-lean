import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSectionVars false

open Complex Matrix

namespace MetriplecticEquilibrium

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 1. Metriplectic Flow Structure on Matrix Operators over M_n(ℂ) -/
structure MetriplecticFlow (n : Type*) [Fintype n] [DecidableEq n] where
  rho : Matrix n n ℂ
  H   : Matrix n n ℂ                        -- Reversible Hamiltonian
  grad_F : Matrix n n ℂ                   -- Free Energy Gradient
  Onsager : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ -- Onsager Mobility
  h_onsager_zero : Onsager 0 = 0          -- Zero gradient yields zero dissipation

/-- 2. Matrix Commutator Operator: [A, B] = A * B - B * A -/
noncomputable def commutator (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

/-- 3. Reversible Unitary Flow: -i [H, ρ] -/
noncomputable def unitaryFlow (H rho : Matrix n n ℂ) : Matrix n n ℂ :=
  - Complex.I • commutator H rho

/-- 4. Full Non-Equilibrium Evolution Equation: ρ̇ = -i[H, ρ] - 𝕄(∇ℱ) -/
noncomputable def stateEvolution (flow : MetriplecticFlow n) : Matrix n n ℂ :=
  unitaryFlow flow.H flow.rho - flow.Onsager flow.grad_F

/-- 🏆 THEOREM 1: At the bottom of the Free Energy manifold (∇ℱ = 0),
    the Metriplectic Flow strictly reduces to Unitary Reversible Evolution. -/
theorem equilibrium_restores_unitary_flow (flow : MetriplecticFlow n)
    (h_equilibrium : flow.grad_F = 0) :
    stateEvolution flow = unitaryFlow flow.H flow.rho := by
  dsimp [stateEvolution]
  rw [h_equilibrium]
  rw [flow.h_onsager_zero]
  exact sub_zero _

/-- 🏆 THEOREM 2: Energy Conservation under Reversible Unitary Flow
    Proves Tr(H * (-i[H, ρ])) = 0 via trace cyclicity. -/
theorem unitary_flow_conserves_energy (H rho : Matrix n n ℂ) :
    trace (H * unitaryFlow H rho) = 0 := by
  dsimp [unitaryFlow, commutator]
  rw [Matrix.mul_smul, trace_smul]
  have h_comm : trace (H * (H * rho - rho * H)) = 0 := by
    calc trace (H * (H * rho - rho * H))
      _ = trace (H * (H * rho) - H * (rho * H)) := by rw [mul_sub]
      _ = trace (H * (H * rho)) - trace (H * (rho * H)) := by rw [trace_sub]
      _ = trace (H * H * rho) - trace (H * rho * H) := by rw [mul_assoc, mul_assoc]
      _ = trace (H * H * rho) - trace (H * H * rho) := by rw [trace_mul_comm (H * rho) H, mul_assoc]
      _ = 0 := sub_self _
  rw [h_comm, smul_zero]

end MetriplecticEquilibrium
