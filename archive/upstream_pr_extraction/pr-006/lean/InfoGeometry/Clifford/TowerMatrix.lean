import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open scoped Matrix
open scoped Kronecker

namespace InfoGeometry.Clifford.TowerMatrix

open Matrix

def Idx : ℕ → Type | 0 => Fin 1 | n+1 => Idx n × Fin 2

instance (n : ℕ) : Fintype (Idx n) := by induction n with | zero => dsimp [Idx]; exact inferInstance | succ _ ih => dsimp [Idx]; exact @instFintypeProd _ _ ih _
instance (n : ℕ) : DecidableEq (Idx n) := by induction n with | zero => dsimp [Idx]; exact inferInstance | succ _ ih => dsimp [Idx]; exact @instDecidableEqProd _ _ ih _
instance (n : ℕ) : Inhabited (Idx n) := by induction n with | zero => dsimp [Idx]; exact inferInstance | succ _ ih => dsimp [Idx]; exact @instInhabitedProd _ _ ih _
instance : Subsingleton (Idx 0) := by dsimp [Idx]; exact inferInstance

abbrev Mat (n : ℕ) : Type := Matrix (Idx n) (Idx n) ℝ

noncomputable def kronPow (A : Matrix (Fin 2) (Fin 2) ℝ) : (n : ℕ) → Mat n
  | 0 => (1 : Mat 0)
  | n+1 => kronPow A n ⊗ₖ A

noncomputable def Jn (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) : Mat n := kronPow J1 n

lemma Jn_sq (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1 : J1 * J1 = 1) : ∀ n : ℕ, (Jn J1 n) * (Jn J1 n) = (1 : Mat n)
  | 0 => by
    dsimp [Jn, kronPow]
    ext i j
    have : i = j := Subsingleton.elim _ _
    subst this
    exact congrArg (fun m : Mat 0 => m i i) (Matrix.mul_one _)
  | n+1 => by
      dsimp [Jn, kronPow]
      show (kronPow J1 n ⊗ₖ J1) * (kronPow J1 n ⊗ₖ J1) = 1
      have ih : kronPow J1 n * kronPow J1 n = 1 := Jn_sq J1 hJ1 n
      rw [← Matrix.mul_kronecker_mul]
      rw [ih, hJ1, Matrix.one_kronecker_one]

noncomputable def cartan (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) (X : Mat n) : Mat n :=
  -((Jn J1 n) * Xᵀ * (Jn J1 n))

lemma cartan_involutive (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Mat n)) (hJt : (Jn J1 n)ᵀ = (Jn J1 n)) :
    Function.Involutive (cartan J1 n) := by
  intro X
  -- shorthand
  set J : Mat n := Jn J1 n
  have hJJ' : J * J = (1 : Mat n) := by simpa [J] using hJJ
  have hJt' : Jᵀ = J := by simpa [J] using hJt

  calc
    cartan J1 n (cartan J1 n X)
        = - (J * (-(J * Xᵀ * J))ᵀ * J) := by
            simp [cartan, J, Matrix.mul_assoc]
    _   = - (J * (-( (J * Xᵀ * J)ᵀ )) * J) := by
            simp [Matrix.transpose_neg, Matrix.mul_assoc]
    _   = J * ((J * Xᵀ * J)ᵀ) * J := by
            simp [Matrix.mul_assoc]
    _   = J * (Jᵀ * X * Jᵀ) * J := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.transpose_transpose]
    _   = J * (J * X * J) * J := by
            simp [hJt', Matrix.mul_assoc]
    _   = (J * J) * X * (J * J) := by
            simp [Matrix.mul_assoc]
    _   = X := by
            simp [hJJ']

section Transpose
lemma transpose_kronecker {m p : Type*} (A : Matrix m m ℝ) (B : Matrix p p ℝ) : (A ⊗ₖ B)ᵀ = (Aᵀ ⊗ₖ Bᵀ) := by
  ext ⟨i,ip⟩ ⟨j,jq⟩; rfl
end Transpose

lemma Jn_transpose (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1t : J1ᵀ = J1) : ∀ n : ℕ, (Jn J1 n)ᵀ = Jn J1 n
  | 0 => by
    dsimp [Jn, kronPow]
    ext i j
    have : i = j := Subsingleton.elim _ _
    subst this
    rfl
  | n+1 => by
      change (kronPow J1 n ⊗ₖ J1)ᵀ = kronPow J1 n ⊗ₖ J1
      rw [transpose_kronecker]
      have ih : (kronPow J1 n)ᵀ = kronPow J1 n := Jn_transpose J1 hJ1t n
      rw [ih, hJ1t]

end InfoGeometry.Clifford.TowerMatrix
