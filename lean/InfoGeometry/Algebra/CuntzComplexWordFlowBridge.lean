/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

/-!
# Complex modular flow on Cuntz word pairs

The complex-time quotient flow is recorded on arbitrary noncommutative word
pairs.  This is the algebraic flow wire needed by a genuine monomial KMS
calculation; it does not define a state or replace quotient multiplication by
a scalar word model.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzComplexWordFlowBridge

open Complex
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

def complexWordPhase (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) :
    List (Fin n) → ℂ
  | [] => 1
  | i :: w => modularPhaseComplex (primes i) z * complexWordPhase n primes z w

def complexWordPhaseInv (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) :
    List (Fin n) → ℂ
  | [] => 1
  | i :: w => modularPhaseComplexInv (primes i) z *
      complexWordPhaseInv n primes z w

theorem sigmaComplex_cuntzS
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (i : Fin n) :
    sigmaComplex n primes z (cuntzS n i) =
      modularPhaseComplex (primes i) z • cuntzS n i := by
  dsimp [cuntzS, cuntzMk]
  rw [sigmaComplex_mk, sigmaTensorComplex_S, map_smul]

theorem sigmaComplex_cuntzSdag
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (i : Fin n) :
    sigmaComplex n primes z (cuntzSdag n i) =
      modularPhaseComplexInv (primes i) z • cuntzSdag n i := by
  dsimp [cuntzSdag, cuntzMk]
  rw [sigmaComplex_mk, sigmaTensorComplex_Sdag, map_smul]

theorem sigmaComplex_cuntzWordShift
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (w : List (Fin n)) :
    sigmaComplex n primes z (cuntzWordShift w) =
      complexWordPhase n primes z w • cuntzWordShift w := by
  induction w with
  | nil => simp [cuntzWordShift, complexWordPhase]
  | cons i w ih =>
      rw [cuntzWordShift, map_mul, sigmaComplex_cuntzS, ih]
      simp [complexWordPhase, smul_smul, mul_comm]

theorem sigmaComplex_cuntzWordShiftDag
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (w : List (Fin n)) :
    sigmaComplex n primes z (cuntzWordShiftDag w) =
      complexWordPhaseInv n primes z w • cuntzWordShiftDag w := by
  induction w with
  | nil => simp [cuntzWordShiftDag, complexWordPhaseInv]
  | cons i w ih =>
      rw [cuntzWordShiftDag, map_mul, ih, sigmaComplex_cuntzSdag]
      simp [complexWordPhaseInv, smul_smul, mul_comm]

theorem sigmaComplex_cuntzWordPair
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ)
    (u v : List (Fin n)) :
    sigmaComplex n primes z (cuntzWordShift u * cuntzWordShiftDag v) =
      (complexWordPhase n primes z u *
          complexWordPhaseInv n primes z v) •
        (cuntzWordShift u * cuntzWordShiftDag v) := by
  rw [map_mul, sigmaComplex_cuntzWordShift,
    sigmaComplex_cuntzWordShiftDag, smul_mul_smul]

theorem complexWordPhase_binary_imag
    (n : ℕ) (β : ℝ) (w : List (Fin n)) :
    complexWordPhase n (fun _ => 2) (I * (β : ℂ)) w =
      List.prod (List.map (fun _i => (2 : ℂ) ^ (-(β : ℂ))) w) := by
  induction w with
  | nil => simp [complexWordPhase]
  | cons i w ih =>
      rw [complexWordPhase, modularPhaseComplex_imag 2 (by norm_num)]
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      norm_num

theorem complexWordPhaseInv_binary_imag
    (n : ℕ) (β : ℝ) (w : List (Fin n)) :
    complexWordPhaseInv n (fun _ => 2) (I * (β : ℂ)) w =
      List.prod (List.map (fun _i => (2 : ℂ) ^ (β : ℂ)) w) := by
  induction w with
  | nil => simp [complexWordPhaseInv]
  | cons i w ih =>
      rw [complexWordPhaseInv, modularPhaseComplexInv_imag 2 (by norm_num)]
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      norm_num

theorem sigmaComplex_cuntzWordPair_binary_imag
    (n : ℕ) (β : ℝ) (u v : List (Fin n)) :
    sigmaComplex n (fun _ => 2) (I * (β : ℂ))
        (cuntzWordShift u * cuntzWordShiftDag v) =
      ((List.prod (List.map (fun _i => (2 : ℂ) ^ (-(β : ℂ))) u)) *
          (List.prod (List.map (fun _i => (2 : ℂ) ^ (β : ℂ)) v))) •
        (cuntzWordShift u * cuntzWordShiftDag v) := by
  rw [sigmaComplex_cuntzWordPair, complexWordPhase_binary_imag,
    complexWordPhaseInv_binary_imag]

end InfoGeometry.Algebra.CuntzComplexWordFlowBridge
