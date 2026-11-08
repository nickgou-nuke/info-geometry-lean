/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.NilpotentPairingAnomalyToChiralBlockGapPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsFiveGradedClosurePoset

/-!
# Matrix-unit realization of the anomaly-to-gap spine

This module instantiates the anomaly-first algebra in the actual noncommutative
operator ring `Matrix (Fin 2) (Fin 2) B`. Its nilpotent generator is a matrix
unit and its adjoint is the reverse matrix unit. No scalar operator surrogate
or commutation assumption is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixUnitAnomalyRealization

open OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset

variable {B : Type*} [Ring B] [StarRing B]

omit [StarRing B] in
private theorem add_four_swap (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := by
      rw [add_assoc a b (c + d)]
    _ = a + ((b + c) + d) := by rw [← add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := by rw [← add_assoc a c (b + d)]

omit [StarRing B] in
private theorem add_four_left_assoc (a b c d : B) :
    ((a + b) + c) + d = (a + c) + (b + d) := by
  calc
    ((a + b) + c) + d = (a + b) + (c + d) := by
      rw [← add_assoc (a + b) c d]
    _ = (a + c) + (b + d) := add_four_swap a b c d

/-- The existing matrix-unit nilpotent, viewed in the star ring of operators. -/
def Nplus : Matrix (Fin 2) (Fin 2) B := !![0, (1 : B); 0, 0]

/-- Its reverse matrix-unit adjoint. -/
def Nminus : Matrix (Fin 2) (Fin 2) B := !![0, 0; (1 : B), 0]

/-- The positive sheet support `N₊ N₊*` in the matrix operator algebra. -/
def P (N : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B := N * star N

/-- The negative sheet support `N₊* N₊` in the matrix operator algebra. -/
def Q (N : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B := star N * N

theorem Nplus_star_eq_Nminus : star (Nplus (B := B)) = Nminus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus, Nminus]

omit [StarRing B] in
theorem Nplus_sq_zero : Nplus (B := B) * Nplus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus, Matrix.mul_apply, Fin.sum_univ_two]

theorem Nplus_regular :
    Nplus (B := B) * star Nplus * Nplus = Nplus := by
  rw [Nplus_star_eq_Nminus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus, Nminus, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing B] in
/-- The two ordered products differ on every nontrivial coefficient ring. -/
theorem Nplus_Nminus_noncommute [Nontrivial B] :
    Nplus (B := B) * Nminus ≠ Nminus * Nplus := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [Nplus, Nminus] at h00

/-- The anomaly-generated Peirce sheets are the two complementary diagonal
matrix-unit supports in this operator representation. -/
theorem matrix_unit_peirce_sheets :
    P (Nplus (B := B)) = !![(1 : B), 0; 0, 0] ∧
    Q (Nplus (B := B)) = !![0, 0; 0, (1 : B)] ∧
    P (Nplus (B := B)) * Q (Nplus (B := B)) = 0 ∧
    Q (Nplus (B := B)) * P (Nplus (B := B)) = 0 ∧
    P (Nplus (B := B)) + Q (Nplus (B := B)) = 1 := by
  have hs := Nplus_star_eq_Nminus (B := B)
  have hP : P (Nplus (B := B)) = !![(1 : B), 0; 0, 0] := by
    change Nplus (B := B) * star Nplus = !![(1 : B), 0; 0, 0]
    rw [hs]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nplus, Nminus, Matrix.mul_apply, Fin.sum_univ_two]
  have hQ : Q (Nplus (B := B)) = !![0, 0; 0, (1 : B)] := by
    change star Nplus * Nplus (B := B) = !![0, 0; 0, (1 : B)]
    rw [hs]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nplus, Nminus, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hP, hQ, ?_, ?_, ?_⟩
  · rw [hP, hQ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [hQ, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [hP, hQ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Every operator in the matrix-unit model is reconstructed from its four
ordered source/target sheet corners. The order of matrix factors is retained. -/
theorem matrix_unit_four_corner_reconstruction (X : Matrix (Fin 2) (Fin 2) B) :
    P (Nplus (B := B)) * X * P (Nplus (B := B)) +
      P (Nplus (B := B)) * X * Q (Nplus (B := B)) +
      Q (Nplus (B := B)) * X * P (Nplus (B := B)) +
      Q (Nplus (B := B)) * X * Q (Nplus (B := B)) = X := by
  have hsum := (matrix_unit_peirce_sheets (B := B)).2.2.2.2
  calc
    _ = (P (Nplus (B := B)) + Q (Nplus (B := B))) * X *
        (P (Nplus (B := B)) + Q (Nplus (B := B))) := by
      let p := P (Nplus (B := B))
      let q := Q (Nplus (B := B))
      change p * X * p + p * X * q + q * X * p + q * X * q =
        (p + q) * X * (p + q)
      have hExpand : (p + q) * X * (p + q) =
          (p * X * p + q * X * p) + (p * X * q + q * X * q) := by
        calc
          (p + q) * X * (p + q) = ((p + q) * X) * p + ((p + q) * X) * q := by
            rw [mul_add]
          _ = ((p * X + q * X) * p) + ((p * X + q * X) * q) := by
            rw [add_mul]
          _ = (p * X * p + q * X * p) + (p * X * q + q * X * q) := by
            rw [add_mul, add_mul]
      calc
        _ = (p * X * p + q * X * p) + (p * X * q + q * X * q) := by
          exact add_four_left_assoc (p * X * p) (p * X * q)
            (q * X * p) (q * X * q)
        _ = (p + q) * X * (p + q) := hExpand.symm
    _ = 1 * X * 1 := by rw [hsum]
    _ = X := by simp

/-- In the matrix-unit realization, the four Peirce corners are exactly the
four matrix entries, each placed in its original source/target position.
This is a coordinate-level form of the four-corner anatomy; it keeps the
coefficient order inside `X` and requires no commutativity of `B`. -/
theorem matrix_unit_peirce_corner_coordinates (X : Matrix (Fin 2) (Fin 2) B) :
    P (Nplus (B := B)) * X * P (Nplus (B := B)) = !![X 0 0, 0; 0, 0] ∧
    P (Nplus (B := B)) * X * Q (Nplus (B := B)) = !![0, X 0 1; 0, 0] ∧
    Q (Nplus (B := B)) * X * P (Nplus (B := B)) = !![0, 0; X 1 0, 0] ∧
    Q (Nplus (B := B)) * X * Q (Nplus (B := B)) = !![0, 0; 0, X 1 1] := by
  have hP := (matrix_unit_peirce_sheets (B := B)).1
  have hQ := (matrix_unit_peirce_sheets (B := B)).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_two]
  · rw [hP, hQ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_two]
  · rw [hQ, hP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_two]
  · rw [hQ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
        Fin.sum_univ_two]

omit [StarRing B] in
/-- The nilpotent matrix unit extracts the lower-left coefficient of an
arbitrary operator and returns it in the upper-right corner. This is the
matrix-coordinate realization of the KKT quadratic sandwich, before its
Jordan-associator factor of two is applied. -/
theorem matrix_unit_nilpotent_sandwich_coordinates
    (X : Matrix (Fin 2) (Fin 2) B) :
    Nplus (B := B) * X * Nplus = !![0, X 1 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nplus, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

omit [StarRing B] in
/-- The abstract KKT grade `+2` Jordan-associator generator is twice the
lower-left matrix coefficient, placed in the upper-right corner. -/
theorem matrix_unit_K_plus2_coordinates (X : Matrix (Fin 2) (Fin 2) B) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.K_plus2
      (Nplus (B := B)) X = 2 • !![0, X 1 0; 0, 0] := by
  rw [InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits.K_plus2_eq_two_sandwich
    (Nplus (B := B)) X Nplus_sq_zero,
    matrix_unit_nilpotent_sandwich_coordinates]

/-- The two matrix-unit sheets fill the whole `2 × 2` operator carrier. -/
theorem Nplus_gap_eq_one : Gap (Nplus (B := B)) = 1 := by
  rw [← Phi_sq_eq_Gap (Nplus (B := B)) (Nplus_sq_zero (B := B))
    (Nplus_regular (B := B))]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Phi, Nplus, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

/-- In this concrete matrix operator algebra, the primitive pair realizes the
parity anomaly, its idempotent support, and the chiral block gap simultaneously. -/
theorem matrix_unit_anomaly_gap_spine (X : Matrix (Fin 2) (Fin 2) B) :
    (OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Sigma
      (Nplus (B := B)) * Nplus = Nplus) ∧
    (Nplus * OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Sigma
      (Nplus (B := B)) = -Nplus) ∧
    (Gap (Nplus (B := B)) * Gap (Nplus (B := B)) = Gap (Nplus (B := B))) ∧
    (Phi (Nplus (B := B)) * Phi (Nplus (B := B)) = Gap (Nplus (B := B))) ∧
    (Phi (Nplus (B := B)) * (Phi (Nplus (B := B)) * Phi (Nplus (B := B)) -
      (1 : Matrix (Fin 2) (Fin 2) B)) = 0) ∧
    (P (Nplus (B := B)) * X * P (Nplus (B := B)) +
      P (Nplus (B := B)) * X * Q (Nplus (B := B)) +
      Q (Nplus (B := B)) * X * P (Nplus (B := B)) +
      Q (Nplus (B := B)) * X * Q (Nplus (B := B)) = X) := by
  have hnil : Nplus (B := B) * Nplus = 0 := Nplus_sq_zero
  have hreg : Nplus (B := B) * star Nplus * Nplus = Nplus := Nplus_regular
  refine ⟨Sigma_mul_N_plus (Nplus (B := B)) hnil hreg,
    N_plus_mul_Sigma (Nplus (B := B)) hnil hreg,
    Gap_idem (Nplus (B := B)) hnil hreg,
    Phi_sq_eq_Gap (Nplus (B := B)) hnil hreg, ?_,
    matrix_unit_four_corner_reconstruction X⟩
  rw [Phi_sq_eq_Gap (Nplus (B := B)) hnil hreg, Nplus_gap_eq_one]
  simp

end InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixUnitAnomalyRealization
