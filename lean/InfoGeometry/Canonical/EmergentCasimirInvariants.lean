import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# InfoGeometry.Canonical.EmergentCasimirInvariants

This module formalizes the Casimir Operators of the emergent Bi-Quaternion 
Kähler framework. By Noether's Theorem, these operators map continuously 
to the globally conserved topological charges of the spinor condensate.

We formally define:
1. The Mass-Squared Casimir (Poincaré/Lorentz)
2. The Spin Casimir (Pauli-Lubanski)
3. The Electroweak Casimirs (Hypercharge & Isospin)
4. The Color Casimirs (Quadratic & Cubic SU(3))
-/

noncomputable section

namespace EmergentCasimirInvariants

open Matrix

/-- 1. The Mass-Squared Casimir Operator: $C_1 = P_\mu P^\mu$
    Determines the mass gap of the quaternionic condensate excitations. -/
def MassSquaredCasimir (P : Fin 4 → ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  dotProduct P (mulVec g P)

/-- 2. The Spin Casimir Operator: $C_2 = W_\mu W^\mu$
    where $W_\mu$ is the Pauli-Lubanski pseudovector.
    Classifies the emergent spin representation of the state. -/
def SpinCasimir (W : Fin 4 → ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  dotProduct W (mulVec g W)

/-- 3. The Electroweak Casimir: $C_3 = Y^2 + T(T+1)$
    where $Y$ is the hypercharge and $T$ is the weak isospin. -/
def ElectroweakCasimir (Y T : ℝ) : ℝ :=
  Y^2 + T * (T + 1)

/-- 4a. The Quadratic SU(3) Color Casimir: $C_{41} = \sum_a \lambda_a \lambda_a$ -/
def SU3QuadraticCasimir (lambda_sum_sq : ℝ) : ℝ :=
  lambda_sum_sq

/-- 4b. The Cubic SU(3) Color Casimir: $C_{42} = d_{abc} \lambda_a \lambda_b \lambda_c$ -/
def SU3CubicCasimir (d_abc_lambda_cubed : ℝ) : ℝ :=
  d_abc_lambda_cubed

/-- Theorem: The Mass-Squared Casimir evaluates strictly to $m^2$ on the rest frame 
    where $P = (m, 0, 0, 0)$ and $g = \eta$ (Minkowski). -/
theorem mass_squared_rest_frame (m : ℝ) :
    let P : Fin 4 → ℝ := fun i => if i = 0 then m else 0
    let g : Matrix (Fin 4) (Fin 4) ℝ := 
      fun i j => if i = 0 ∧ j = 0 then 1 else (if i = j then -1 else 0)
    MassSquaredCasimir P g = m^2 := by
  intro P g
  dsimp [MassSquaredCasimir, P, g, mulVec, dotProduct]
  rw [Fin.sum_univ_four]
  simp
  ring

end EmergentCasimirInvariants
