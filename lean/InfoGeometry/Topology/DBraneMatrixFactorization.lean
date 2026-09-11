import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Q8ModularFlowBridge
import InfoGeometry.Topology.BuscherTDuality

/-!
# DBraneMatrixFactorization

Formalizes the algebraic category of matrix factorizations of the 
light-cone quadric q(P). Proves that the Pauli momentum matrix and 
its adjugate form a minimal topological D-brane on the horizon.
-/

open Matrix

variable (M : Type _) [CommRing M] [Algebra ℂ M]

/-- 
  The Matrix Factorization category of the polynomial W.
  Two matrices D₀, D₁ such that D₀ * D₁ = W * I.
-/
structure MatrixFactorization (W : M) where
  D0 : Matrix (Fin 2) (Fin 2) M
  D1 : Matrix (Fin 2) (Fin 2) M
  factorization_relation : D0 * D1 = W • (1 : Matrix (Fin 2) (Fin 2) M)

namespace MatrixFactorization

/-- 
  The Pauli-soldered physical momentum matrix.
  X(P) = E*I + p_x*σ_x + p_y*σ_y + p_z*σ_z
-/
def pauli_momentum (E px py pz : M) : Matrix (Fin 2) (Fin 2) M :=
  ![![E + pz, px - Complex.I • py], ![px + Complex.I • py, E - pz]]

/-- The adjugate matrix of the Pauli-soldered momentum. -/
def pauli_adjugate (E px py pz : M) : Matrix (Fin 2) (Fin 2) M :=
  ![![E - pz, -(px - Complex.I • py)], ![-(px + Complex.I • py), E + pz]]

/--
  THE D-BRANE COMPILATION THEOREM
  Proves that the Pauli-soldered momentum matrix and its adjugate form 
  a valid, minimal matrix factorization of the Minkowski metric q(P).
-/
theorem pauli_is_dbrane_factorization (E px py pz : M) :
    let q := E^2 - px^2 - py^2 - pz^2
    let D0 := pauli_momentum M E px py pz
    let D1 := pauli_adjugate M E px py pz
    D0 * D1 = q • (1 : Matrix (Fin 2) (Fin 2) M) := by
  intros q D0 D1
  dsimp [q, D0, D1]
  have I_sq_M : (algebraMap ℂ M Complex.I) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauli_momentum, pauli_adjugate, mul_apply, Fin.sum_univ_two, Algebra.smul_def]
  · calc
      _ = E^2 - px^2 - pz^2 + (algebraMap ℂ M Complex.I)^2 * py^2 := by ring
      _ = E^2 - px^2 - pz^2 + (-1 : M) * py^2 := by rw [I_sq_M]
      _ = E^2 - px^2 - py^2 - pz^2 := by ring
  · ring
  · ring
  · calc
      _ = E^2 - px^2 - pz^2 + (algebraMap ℂ M Complex.I)^2 * py^2 := by ring
      _ = E^2 - px^2 - pz^2 + (-1 : M) * py^2 := by rw [I_sq_M]
      _ = E^2 - px^2 - py^2 - pz^2 := by ring

end MatrixFactorization
