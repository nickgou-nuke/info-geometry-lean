import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Singular.MoorePenroseAdjoint
import InfoGeometry.Clifford.Decomposition

namespace InfoGeometry.Singular.CartanWiring

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Decomposition
open InfoGeometry.Singular.MoorePenroseAdjoint
open Matrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)
variable (hJ1_sq : J1 * J1 = 1)
variable (hJ1t : J1ᵀ = J1)

/-- 
The "Nuke" Wiring: Proves that the anti-automorphism engine φ 
satisfies the AdjointLike axioms required for the Moore-Penrose Geometric Mirror.
-/
noncomputable instance CartanAdjoint : AdjointLike (TowerMatrix.Mat n) where
  adj := Decomposition.φ J1
  invol := by 
    intro A
    have hJJ : TowerMatrix.Jn J1 n * TowerMatrix.Jn J1 n = 1 := TowerMatrix.Jn_sq J1 hJ1_sq n
    have hJt : (TowerMatrix.Jn J1 n)ᵀ = TowerMatrix.Jn J1 n := TowerMatrix.Jn_transpose J1 hJ1t n
    dsimp [Decomposition.φ, Decomposition.J]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hJt]
    -- J A^T J -> J (J A^T J)^T J = J (J^T A J^T) J = J J A J J
    -- Currently the LHS is J * (J * A * J) * J
    -- we want to turn it into A.
    rw [← Matrix.mul_assoc (TowerMatrix.Jn J1 n) (TowerMatrix.Jn J1 n) (A * TowerMatrix.Jn J1 n)]
    rw [hJJ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  mul_rev := by
    intro A B
    exact φ_mul_rev J1 hJ1_sq A B
  add := by intro A B; dsimp [Decomposition.φ, Decomposition.J]; simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  one := by dsimp [Decomposition.φ, Decomposition.J]; simp [Matrix.transpose_one, TowerMatrix.Jn_sq J1 hJ1_sq n]
  zero := by dsimp [Decomposition.φ, Decomposition.J]; simp
  neg := by intro A; dsimp [Decomposition.φ, Decomposition.J]; simp [Matrix.transpose_neg]

end InfoGeometry.Singular.CartanWiring
