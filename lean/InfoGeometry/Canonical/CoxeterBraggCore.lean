/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open Matrix

namespace InfoGeometry.Canonical.CoxeterBraggCore

variable {A : Type*} [Ring A] [StarRing A]

def projectedShadow (P X : A) : A := P * X * P

def transferParPerp (P X : A) : A := P * X * (1 - P)

def transferPerpPar (P X : A) : A := (1 - P) * X * P

def braggStructureFactor (P X : A) : A :=
  transferParPerp P X * transferPerpPar P X

/-- The transfer corners are square-zero for every idempotent cut. -/
theorem transfer_square_zero {P X : A} (hP : P * P = P) :
    transferParPerp P X * transferParPerp P X = 0 ∧
    transferPerpPar P X * transferPerpPar P X = 0 := by
  have hLP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hPL : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  constructor
  · unfold transferParPerp
    calc
      (P * X * (1 - P)) * (P * X * (1 - P)) =
          P * X * ((1 - P) * P) * X * (1 - P) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hLP, mul_zero, zero_mul, zero_mul]
  · unfold transferPerpPar
    calc
      ((1 - P) * X * P) * ((1 - P) * X * P) =
          (1 - P) * X * (P * (1 - P)) * X * P := by
            simp only [mul_assoc]
      _ = 0 := by rw [hPL, mul_zero, zero_mul, zero_mul]

/-- Exact noncommutative cut-and-project defect identity. -/
theorem projected_square_defect {P X : A} (hP : P * P = P) :
    projectedShadow P (X * X) - projectedShadow P X * projectedShadow P X =
      braggStructureFactor P X := by
  have hperp : (1 - P) * (1 - P) = 1 - P := by
    have hPL : P * (1 - P) = 0 := by
      rw [mul_sub, mul_one, hP, sub_self]
    rw [sub_mul, one_mul, hPL, sub_zero]
  unfold projectedShadow braggStructureFactor transferParPerp transferPerpPar
  calc
    P * (X * X) * P - (P * X * P) * (P * X * P) =
        P * X * (1 - P * P) * X * P := by noncomm_ring
    _ = P * X * (1 - P) * X * P := by rw [hP]
    _ = P * X * ((1 - P) * (1 - P)) * X * P := by rw [hperp]
    _ = (P * X * (1 - P)) * ((1 - P) * X * P) := by
      simp only [mul_assoc]

/-- In a `StarRing`, self-adjoint cut and operator make the defect self-adjoint.

No order or positivity is assumed here: “positive semidefinite” needs an
additional ordered `*`-algebra hypothesis. -/
theorem star_bragg_factor {P X : A}
    (hP : P * P = P) (hPstar : star P = P) (hXstar : star X = X) :
    transferPerpPar P X = star (transferParPerp P X) ∧
    star (braggStructureFactor P X) = braggStructureFactor P X := by
  have hperpstar : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hPstar]
  have hdual : transferPerpPar P X = star (transferParPerp P X) := by
    unfold transferPerpPar transferParPerp
    rw [star_mul, star_mul, hperpstar, hXstar, hPstar, mul_assoc]
  constructor
  · exact hdual
  · unfold braggStructureFactor
    rw [hdual, star_mul, star_star]

/-! A concrete noncommutative witness: the transfer factor need not vanish. -/

def fin2Cut : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

def fin2Swap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem fin2_cut_idempotent : fin2Cut * fin2Cut = fin2Cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fin2Cut, Matrix.mul_apply, Fin.sum_univ_succ]

theorem fin2_perp : (1 - fin2Cut : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fin2Cut, Matrix.one_apply]

theorem fin2_bragg_factor_nonzero :
    braggStructureFactor fin2Cut fin2Swap = fin2Cut ∧
    braggStructureFactor fin2Cut fin2Swap ≠ 0 := by
  have hfactor : braggStructureFactor fin2Cut fin2Swap = fin2Cut := by
    unfold braggStructureFactor transferParPerp transferPerpPar
    rw [fin2_perp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fin2Cut, fin2Swap, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_two]
  refine ⟨hfactor, ?_⟩
  rw [hfactor]
  intro hz
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hz
  norm_num [fin2Cut] at hentry

end InfoGeometry.Canonical.CoxeterBraggCore
