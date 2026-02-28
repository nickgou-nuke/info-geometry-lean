import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Clifford.Decomposition

namespace InfoGeometry.Singular

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Decomposition
open Matrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)
variable (hJ1_sq : J1 * J1 = 1)
variable (hJ1t : J1ᵀ = J1)

/-- 
The "Nuke" Wiring: Proves that the anti-automorphism engine φ 
satisfies the AdjointLike axioms required for the Moore-Penrose Geometric Mirror.
-/
noncomputable def CartanAdjoint : AdjointLike (TowerMatrix.Mat n) where
  adj := φ J1 n
  invol := by 
    intro A
    have hJJ : TowerMatrix.Jn J1 n * TowerMatrix.Jn J1 n = 1 := TowerMatrix.Jn_sq J1 hJ1_sq n
    have hJt : (TowerMatrix.Jn J1 n)ᵀ = TowerMatrix.Jn J1 n := TowerMatrix.Jn_transpose J1 hJ1t n
    simp [φ, Matrix.transpose_mul, Matrix.transpose_transpose, hJt, Matrix.mul_assoc, J]
    conv_lhs => rw [←Matrix.mul_one (TowerMatrix.Jn J1 n * A), ←hJJ]
    simp [Matrix.mul_assoc]
  mul_rev := by
    intro A B
    exact φ_mul_rev J1 hJ1_sq A B
  add := by intro A B; simp [φ, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, J]
  one := by simp [φ, TowerMatrix.Jn_sq J1 hJ1_sq n, J]
  zero := by simp [φ, J]
  neg := by intro A; simp [φ, J]

end InfoGeometry.Singular
