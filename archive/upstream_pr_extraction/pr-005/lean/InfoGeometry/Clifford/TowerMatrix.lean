import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open scoped Matrix
open scoped Kronecker

namespace InfoGeometry.Clifford.TowerMatrix

open Matrix

def Idx : ℕ → Type | 0 => PUnit | n+1 => Idx n × Fin 2

instance (n : ℕ) : Fintype (Idx n) := by induction n with | zero => infer_instance | succ n ih => dsimp [Idx]; infer_instance
instance (n : ℕ) : DecidableEq (Idx n) := by induction n with | zero => infer_instance | succ n ih => dsimp [Idx]; infer_instance

abbrev Mat (n : ℕ) : Type := Matrix (Idx n) (Idx n) ℝ

noncomputable def kronPow (A : Matrix (Fin 2) (Fin 2) ℝ) : (n : ℕ) → Mat n
  | 0 => (1 : Mat 0)
  | n+1 => kronPow A n ⊗ₖ A

noncomputable def Jn (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) : Mat n := kronPow J1 n

lemma Jn_sq (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1 : J1 * J1 = 1) : ∀ n : ℕ, (Jn J1 n) * (Jn J1 n) = (1 : Mat n)
  | 0 => by simp [Jn, kronPow]
  | n+1 => by 
      simp [Jn, kronPow]
      rw [Matrix.mul_kronecker_mul]
      simp [Jn_sq J1 hJ1 n, hJ1]

noncomputable def cartan (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (X : Mat n) : Mat n :=
  - (Jn J1 n) * Xᵀ * (Jn J1 n)

lemma cartan_involutive (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Mat n)) (hJt : (Jn J1 n)ᵀ = (Jn J1 n)) :
    Function.Involutive (cartan J1 n) := by
  intro X
  simp [cartan, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_neg, hJt, hJJ, Matrix.mul_assoc]

section Transpose
variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
lemma transpose_kronecker (A : Matrix m m ℝ) (B : Matrix p p ℝ) : (A ⊗ₖ B)ᵀ = (Aᵀ ⊗ₖ Bᵀ) := by
  ext ⟨i,ip⟩ ⟨j,jq⟩; simp [Matrix.kronecker_apply, Matrix.transpose_apply]
end Transpose

lemma Jn_transpose (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1t : J1ᵀ = J1) : ∀ n : ℕ, (Jn J1 n)ᵀ = Jn J1 n
  | 0 => by simp [Jn, kronPow]
  | n+1 => by simpa [Jn, kronPow, transpose_kronecker, Jn_transpose J1 hJ1t n, hJ1t]

end InfoGeometry.Clifford.TowerMatrix
