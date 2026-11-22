/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.HadamardBlockTower

/-!
# Operator quasideterminants of `2 × 2` matrices over a noncommutative ring

Extends the owner `HadamardBlockTower` (`opMat2`, `formalAdjugate2`, `schurComplement11`,
`schur_complement_ldu`, `manin_left_cramer`, `hadamard_schur_sandwich`) over an arbitrary ring.

* The naive determinant really fails: on `2 × 2` integer operator matrices the singular
  factorized matrix `!![1, b; c, c b]` has `1·(c b) - b c ≠ 0`.
* Dieudonné left determinant: `a · |M|₁₁ = (a d - c b) - [a, c] a⁻¹ b`.
* Banachiewicz inverse: with two-sided inverses of `a` and of `|M|₁₁ = d - c a⁻¹ b`, the explicit
  quasideterminant inverse is a two-sided inverse of `M`.
* Hua's identity: `(a - b d⁻¹ c) (a⁻¹ + a⁻¹ b |M|₁₁⁻¹ c a⁻¹) = 1` (left inverse of `d` suffices).
* Bisymmetric Hadamard inversion from left inverses of `x + y`, `x - y`.

## BUCKET 1: Noncommutative ring identities
The Schur complement, determinant correction, inverse, and Hua identity are
proved under the explicit pivot and inverse hypotheses shown in their types.

## BUCKET 2: Finite concrete witness
The integer-matrix example establishes a singularity/commutator counterexample
only for the displayed `2 × 2` matrices over `ℤ`.

## BUCKET 3: Interpretations not established here
No operator topology, spectral theory, quantum determinant classification,
physical interpretation, or lattice construction is established by this file.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorQuasideterminant

open Matrix
open InfoGeometry.OperatorAlgebra.HadamardBlockTower

section General

variable {A : Type*} [Ring A]

/-- Dieudonné left determinant: `a (d - c a⁻¹ b) = (a d - c b) - [a, c] a⁻¹ b`. -/
theorem dieudonne_left (a b c d aInv : A) (hR : a * aInv = 1) :
    a * schurComplement11 b c d aInv = (a * d - c * b) - opCommutator a c * aInv * b := by
  simp only [schurComplement11, opCommutator]
  have h : a * (c * aInv * b) = a * c * aInv * b := by noncomm_ring
  have h' : c * a * aInv * b = c * b := by rw [mul_assoc c a aInv, hR, mul_one]
  rw [mul_sub, h]
  calc a * d - a * c * aInv * b = a * d - c * b - (a * c * aInv * b - c * a * aInv * b) := by
        rw [h']; abel
    _ = a * d - c * b - (a * c - c * a) * aInv * b := by noncomm_ring

/-- The Banachiewicz–quasideterminant inverse. -/
def quasiInv (b c aInv sInv : A) : Matrix (Fin 2) (Fin 2) A :=
  opMat2 (aInv + aInv * b * sInv * c * aInv) (-(aInv * b * sInv)) (-(sInv * c * aInv)) sInv

/-- Express the explicit inverse as the product of the inverse upper, diagonal,
and lower triangular factors from the Schur-complement LDU decomposition. -/
theorem quasiInv_eq_UDL (b c aInv sInv : A) :
    quasiInv b c aInv sInv =
      (opMat2 1 (-(aInv * b)) 0 1 * opMat2 aInv 0 0 sInv) * opMat2 1 0 (-(c * aInv)) 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quasiInv, opMat2, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

/-- **Two-sided inverse** of a `2 × 2` operator matrix from its pivot and its quasideterminant. -/
theorem quasiInv_two_sided (a b c d aInv sInv : A) (haL : aInv * a = 1) (haR : a * aInv = 1)
    (hsL : sInv * schurComplement11 b c d aInv = 1) (hsR : schurComplement11 b c d aInv * sInv = 1) :
    opMat2 a b c d * quasiInv b c aInv sInv = 1 ∧ quasiInv b c aInv sInv * opMat2 a b c d = 1 := by
  set s := schurComplement11 b c d aInv
  have L1 : opMat2 1 0 (c * aInv) 1 * opMat2 1 0 (-(c * aInv)) 1 = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have L2 : opMat2 1 0 (-(c * aInv)) 1 * opMat2 1 0 (c * aInv) 1 = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have U1 : opMat2 1 (aInv * b) 0 1 * opMat2 1 (-(aInv * b)) 0 1 = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have U2 : opMat2 1 (-(aInv * b)) 0 1 * opMat2 1 (aInv * b) 0 1 = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have D1 : opMat2 a 0 0 s * opMat2 aInv 0 0 sInv = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two, haR, hsR]
  have D2 : opMat2 aInv 0 0 sInv * opMat2 a 0 0 s = (1 : Matrix (Fin 2) (Fin 2) A) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two, haL, hsL]
  have hM := schur_complement_ldu a b c d aInv haL haR
  rw [← hM, quasiInv_eq_UDL]
  constructor
  · calc opMat2 1 0 (c * aInv) 1 * opMat2 a 0 0 s * opMat2 1 (aInv * b) 0 1 *
          (opMat2 1 (-(aInv * b)) 0 1 * opMat2 aInv 0 0 sInv * opMat2 1 0 (-(c * aInv)) 1)
        = opMat2 1 0 (c * aInv) 1 * (opMat2 a 0 0 s * (opMat2 1 (aInv * b) 0 1 *
            opMat2 1 (-(aInv * b)) 0 1) * opMat2 aInv 0 0 sInv) * opMat2 1 0 (-(c * aInv)) 1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [U1, Matrix.mul_one, D1, Matrix.mul_one, L1]
  · calc opMat2 1 (-(aInv * b)) 0 1 * opMat2 aInv 0 0 sInv * opMat2 1 0 (-(c * aInv)) 1 *
          (opMat2 1 0 (c * aInv) 1 * opMat2 a 0 0 s * opMat2 1 (aInv * b) 0 1)
        = opMat2 1 (-(aInv * b)) 0 1 * (opMat2 aInv 0 0 sInv * (opMat2 1 0 (-(c * aInv)) 1 *
            opMat2 1 0 (c * aInv) 1) * opMat2 a 0 0 s) * opMat2 1 (aInv * b) 0 1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [L2, Matrix.mul_one, D2, Matrix.mul_one, U2]

/-- **Hua's identity:** `(a - b d⁻¹ c)(a⁻¹ + a⁻¹ b |M|₁₁⁻¹ c a⁻¹) = 1`. -/
theorem hua_identity (a b c d aInv sInv dInv : A) (haL : aInv * a = 1) (haR : a * aInv = 1)
    (hsL : sInv * schurComplement11 b c d aInv = 1) (hsR : schurComplement11 b c d aInv * sInv = 1)
    (hdL : dInv * d = 1) :
    (a - b * dInv * c) * (aInv + aInv * b * sInv * c * aInv) = 1 := by
  have h := (quasiInv_two_sided a b c d aInv sInv haL haR hsL hsR).1
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [opMat2, quasiInv, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  set u := aInv + aInv * b * sInv * c * aInv
  set v := sInv * c * aInv
  -- `h00 : a u - b v = 1`, `h10 : c u - d v = 0`
  have hdv : d * v = c * u := by
    rw [← sub_eq_add_neg, sub_eq_zero] at h10; exact h10.symm
  have hv : v = dInv * (c * u) := by rw [← hdv, ← mul_assoc, hdL, one_mul]
  calc (a - b * dInv * c) * u = a * u - b * (dInv * (c * u)) := by noncomm_ring
    _ = a * u - b * v := by rw [hv]
    _ = 1 := by simpa [sub_eq_add_neg] using h00

/-- Bisymmetric Hadamard inversion from left inverses of the two Hadamard blocks. -/
theorem bisym_hadamard_inverse (x y up um : A) (hp : up * (x + y) = 1) (hm : um * (x - y) = 1) :
    opMat2 (up + um) (up - um) (up - um) (up + um) * opMat2 x y y x = (2 : A) • 1 := by
  have e1 : (up + um) * x + (up - um) * y = up * (x + y) + um * (x - y) := by noncomm_ring
  have e2 : (up + um) * y + (up - um) * x = up * (x + y) - um * (x - y) := by noncomm_ring
  have e3 : (up - um) * x + (up + um) * y = up * (x + y) - um * (x - y) := by noncomm_ring
  have e4 : (up - um) * y + (up + um) * x = up * (x + y) + um * (x - y) := by noncomm_ring
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [opMat2, Matrix.mul_apply, Fin.sum_univ_two, e1, e2, e3, e4, hp, hm] <;>
    norm_num

end General

/-! ### The naive determinant fails on operator matrices -/

section Witness

/-- Operator entries: elementary `2 × 2` integer matrices. -/
def opB : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
/-- A second elementary integer operator that does not commute with `opB`. -/
def opC : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Noncommutativity witness of the operator carrier. -/
theorem opC_opB_ne : opC * opB ≠ opB * opC := by decide

/-- **The naive determinant is not a determinant over operators:** the matrix
`!![1, b; c, c b]` is left-singular, yet `1·(c b) - b c ≠ 0`. -/
theorem naive_det_fails :
    opMat2 (-opC) 1 0 0 * opMat2 1 opB opC (opC * opB) = 0 ∧ 1 * (opC * opB) - opB * opC ≠ 0 := by
  refine ⟨(factorized_operator_matrix_aporia opB opC).1, ?_⟩
  decide

end Witness

end InfoGeometry.OperatorAlgebra.OperatorQuasideterminant
