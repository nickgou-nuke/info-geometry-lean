import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

namespace CPTCausalCone

open Matrix

abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Scale signum generator ε (ε² = +1) -/
def eps : M2Z := ![![0, 1], ![1, 0]]

theorem eps_sq_eq_one : eps ^ 2 = 1 := by decide

/-- Modular glide J (J² = -1) -/
def J : M2Z := ![![0, -1], ![1, 0]]

theorem J_sq_eq_neg_one : J ^ 2 = -1 := by decide

/-- The causal tripotent projector of the DAG node.
    It maps a cognitive state into the future (+1), past (-1), or void (0) -/
def Trip : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 0, 0], ![0, -1, 0], ![0, 0, 0]]

theorem tripotent_Trip : Trip ^ 3 - Trip = 0 := by decide

end CPTCausalCone
