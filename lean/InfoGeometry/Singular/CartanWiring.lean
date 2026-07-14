import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Clifford.Decomposition

namespace CartanWiring

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Decomposition
open Matrix

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- 
Cartan involution viewed as an adjoint-like anti-automorphism on matrix towers.
-/
noncomputable def CartanAdjoint (A : TowerMatrix.Mat n) : TowerMatrix.Mat n :=
  Decomposition.φ J1 A

@[simp] theorem CartanAdjoint_mul (hJ1_sq : J1 * J1 = 1) (A B : TowerMatrix.Mat n) :
    CartanAdjoint (J1 := J1) (n := n) (A * B)
      = CartanAdjoint (J1 := J1) (n := n) B * CartanAdjoint (J1 := J1) (n := n) A := by
  dsimp [CartanAdjoint]
  exact φ_mul_rev J1 hJ1_sq A B

@[simp] theorem CartanAdjoint_add (A B : TowerMatrix.Mat n) :
    CartanAdjoint (J1 := J1) (n := n) (A + B)
      = CartanAdjoint (J1 := J1) (n := n) A + CartanAdjoint (J1 := J1) (n := n) B := by
  dsimp [CartanAdjoint, Decomposition.φ, Decomposition.J]
  simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem CartanAdjoint_zero :
    CartanAdjoint (J1 := J1) (n := n) (0 : TowerMatrix.Mat n) = 0 := by
  dsimp [CartanAdjoint, Decomposition.φ, Decomposition.J]
  simp

@[simp] theorem CartanAdjoint_one :
    (hJ1_sq : J1 * J1 = 1) →
    CartanAdjoint (J1 := J1) (n := n) (1 : TowerMatrix.Mat n) = 1 := by
  intro hJ1_sq
  dsimp [CartanAdjoint, Decomposition.φ, Decomposition.J]
  simp [Matrix.transpose_one, TowerMatrix.Jn_sq J1 hJ1_sq n]

@[simp] theorem CartanAdjoint_neg (A : TowerMatrix.Mat n) :
    CartanAdjoint (J1 := J1) (n := n) (-A)
      = -CartanAdjoint (J1 := J1) (n := n) A := by
  dsimp [CartanAdjoint, Decomposition.φ, Decomposition.J]
  simp [Matrix.transpose_neg]

@[simp] theorem CartanAdjoint_involutive (A : TowerMatrix.Mat n) :
    (hJ1_sq : J1 * J1 = 1) →
    (hJ1t : J1ᵀ = J1) →
    CartanAdjoint (J1 := J1) (n := n) (CartanAdjoint (J1 := J1) (n := n) A) = A := by
  intro hJ1_sq hJ1t
  have hJJ : TowerMatrix.Jn J1 n * TowerMatrix.Jn J1 n = 1 := TowerMatrix.Jn_sq J1 hJ1_sq n
  have hJt : (TowerMatrix.Jn J1 n)ᵀ = TowerMatrix.Jn J1 n := TowerMatrix.Jn_transpose J1 hJ1t n
  dsimp [CartanAdjoint, Decomposition.φ, Decomposition.J]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hJt]
  rw [← Matrix.mul_assoc (TowerMatrix.Jn J1 n) (TowerMatrix.Jn J1 n) (A * TowerMatrix.Jn J1 n)]
  rw [hJJ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]

end CartanWiring
