import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSectionVars false

open Complex Matrix

namespace MetriplecticDissipation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Metriplectic System with explicit Free Energy invariance along unitary orbits -/
structure MetriplecticDissipativeSystem (n : Type*) [Fintype n] [DecidableEq n] where
  rho : Matrix n n ℂ
  H   : Matrix n n ℂ                        -- Reversible Hamiltonian
  grad_F : Matrix n n ℂ                   -- Free Energy Gradient
  Onsager : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ -- Onsager Mobility
  h_onsager_pos : ∀ A : Matrix n n ℂ, 0 ≤ (trace (star A * Onsager A)).re
  -- Metriplectic Degeneracy Condition: Unitary flow preserves Free Energy
  h_unitary_F_inv : (trace (star grad_F * (- Complex.I • (H * rho - rho * H)))).re = 0

/-- Commutator operator [A, B] = A * B - B * A -/
noncomputable def commutator (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

/-- Reversible Unitary Flow: -i [H, ρ] -/
noncomputable def unitaryFlow (H rho : Matrix n n ℂ) : Matrix n n ℂ :=
  - Complex.I • commutator H rho

/-- Full State Evolution ρ̇ = -i[H, ρ] - 𝕄(∇ℱ) -/
noncomputable def stateEvolution (sys : MetriplecticDissipativeSystem n) : Matrix n n ℂ :=
  unitaryFlow sys.H sys.rho - sys.Onsager sys.grad_F

/-- Rate of Free Energy change: dℱ/dt = Re(Tr((∇ℱ)* * ρ̇)) -/
noncomputable def freeEnergyRate (sys : MetriplecticDissipativeSystem n) : ℝ :=
  (trace (star sys.grad_F * stateEvolution sys)).re

/-- 🏆 THEOREM: Non-Positive Rate of Free Energy Change (dℱ/dt ≤ 0)
    Under positive-semidefinite Onsager mobility and unitary free-energy conservation,
    the rate of change of free energy is strictly non-positive (dℱ/dt ≤ 0). -/
theorem freeEnergy_rate_nonpos (sys : MetriplecticDissipativeSystem n) :
    freeEnergyRate sys ≤ 0 := by
  dsimp [freeEnergyRate, stateEvolution, unitaryFlow, commutator]
  rw [mul_sub, trace_sub, Complex.sub_re]
  have h_un : (trace (star sys.grad_F * (-Complex.I • (sys.H * sys.rho - sys.rho * sys.H)))).re = 0 :=
    sys.h_unitary_F_inv
  rw [h_un, zero_sub]
  have h_pos := sys.h_onsager_pos sys.grad_F
  linarith

end MetriplecticDissipation
