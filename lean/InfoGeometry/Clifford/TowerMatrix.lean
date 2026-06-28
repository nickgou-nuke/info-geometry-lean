import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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

/-- The recursive binary tensor index has exactly the full spinor dimension
`2^n`. -/
theorem idx_card_pow_two (n : ℕ) :
    Fintype.card (Idx n) = 2 ^ n := by
  induction n with
  | zero =>
      simp [Idx]
  | succ n ih =>
      simp [Idx, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- Noncomputable cardinality equivalence between the tensor index and the
standard full spinor index `Fin (2^n)`. -/
noncomputable def idxEquivFinPowTwo (n : ℕ) : Idx n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (idx_card_pow_two n)

/-- Reindexing equivalence from the tensor-stage matrix algebra to the standard
full spinor matrix algebra of dimension `2^n`. -/
noncomputable def matEquivFinPowTwo (n : ℕ) :
    Mat n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (idxEquivFinPowTwo n)

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

/--
Cartan involution intertwines with the canonical matrix inverse.
This is the matrix-level compatibility needed to connect `ModularMirror` and Cartan wiring.
-/
lemma cartan_inv_of_isUnit (J1 : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)
    (hJJ : (Jn J1 n) * (Jn J1 n) = (1 : Mat n)) (_hJt : (Jn J1 n)ᵀ = (Jn J1 n))
    {X : Mat n} (hX : IsUnit X.det) :
    cartan J1 n X⁻¹ = (cartan J1 n X)⁻¹ := by
  set J : Mat n := Jn J1 n
  have hJJ' : J * J = (1 : Mat n) := by simpa [J] using hJJ
  have hJinv : J⁻¹ = J := by
    simpa using (Matrix.inv_eq_left_inv (A := J) (B := J) hJJ')
  have hXt : IsUnit (Xᵀ).det := Matrix.isUnit_det_transpose (A := X) hX
  have hJdet : IsUnit J.det := Matrix.isUnit_det_of_left_inverse (A := J) (B := J) hJJ'
  have hA : IsUnit (J * Xᵀ * J).det := by
    simpa [Matrix.det_mul, Matrix.mul_assoc] using (hJdet.mul (hXt.mul hJdet))
  have hneg_inv : (-(J * Xᵀ * J))⁻¹ = -((J * Xᵀ * J)⁻¹) := by
    apply Matrix.inv_eq_left_inv (A := -(J * Xᵀ * J)) (B := -((J * Xᵀ * J)⁻¹))
    calc
      (-((J * Xᵀ * J)⁻¹)) * (-(J * Xᵀ * J))
          = (J * Xᵀ * J)⁻¹ * (J * Xᵀ * J) := by simp
      _ = 1 := Matrix.nonsing_inv_mul (A := J * Xᵀ * J) hA
  calc
    cartan J1 n X⁻¹
        = -(J * (X⁻¹)ᵀ * J) := by simp [cartan, J]
    _ = -(J * (Xᵀ)⁻¹ * J) := by
          simp [Matrix.transpose_nonsing_inv]
    _ = -((J * Xᵀ * J)⁻¹) := by
          have hmul : (J * Xᵀ * J)⁻¹ = J * (Xᵀ)⁻¹ * J := by
            calc
              (J * Xᵀ * J)⁻¹
                  = ((J * Xᵀ) * J)⁻¹ := by simp [Matrix.mul_assoc]
              _ = J⁻¹ * (J * Xᵀ)⁻¹ := by simp [Matrix.mul_inv_rev]
              _ = J⁻¹ * ((Xᵀ)⁻¹ * J⁻¹) := by simp [Matrix.mul_inv_rev]
              _ = J * (Xᵀ)⁻¹ * J := by simp [hJinv, Matrix.mul_assoc]
          rw [hmul]
    _ = (cartan J1 n X)⁻¹ := by
          calc
            -((J * Xᵀ * J)⁻¹) = (-(J * Xᵀ * J))⁻¹ := by simpa using hneg_inv.symm
            _ = (cartan J1 n X)⁻¹ := by simp [cartan, J, Matrix.mul_assoc]

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
