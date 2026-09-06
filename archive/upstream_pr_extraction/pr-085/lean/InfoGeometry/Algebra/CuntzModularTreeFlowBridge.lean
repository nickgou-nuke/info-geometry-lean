import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

/-!
# Modular flow on the finite Cuntz tree

The existing Bost--Connes/Cuntz automorphism is transported to word shifts and
the finite diagonal expectation.  This is an algebraic bridge only: no
topological completion or unbounded modular generator is introduced.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzModularTreeFlowBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.Algebra.CuntzConditionalExpectation
open scoped BigOperators

variable {n : ℕ} (primes : Fin n → ℕ) (t : ℝ)

def wordPhase : List (Fin n) → ℂ
  | [] => 1
  | i :: w => modularPhase (primes i) t * wordPhase w

def wordPhaseInv : List (Fin n) → ℂ
  | [] => 1
  | i :: w => modularPhaseInv (primes i) t * wordPhaseInv w

theorem wordPhase_append (w₁ w₂ : List (Fin n)) :
    wordPhase primes t (w₁ ++ w₂) =
      wordPhase primes t w₁ * wordPhase primes t w₂ := by
  induction w₁ with
  | nil => simp [wordPhase]
  | cons i w ih =>
      simp [wordPhase, ih, mul_assoc]

theorem wordPhaseInv_append (w₁ w₂ : List (Fin n)) :
    wordPhaseInv primes t (w₁ ++ w₂) =
      wordPhaseInv primes t w₁ * wordPhaseInv primes t w₂ := by
  induction w₁ with
  | nil => simp [wordPhaseInv]
  | cons i w ih =>
      simp [wordPhaseInv, ih, mul_assoc]

theorem wordPhase_add (w : List (Fin n)) (s : ℝ) :
    wordPhase primes (t + s) w =
      wordPhase primes t w * wordPhase primes s w := by
  induction w with
  | nil => simp [wordPhase]
  | cons i w ih =>
      simp [wordPhase, modularPhase_add, ih, mul_assoc, mul_left_comm]

theorem wordPhaseInv_add (w : List (Fin n)) (s : ℝ) :
    wordPhaseInv primes (t + s) w =
      wordPhaseInv primes t w * wordPhaseInv primes s w := by
  induction w with
  | nil => simp [wordPhaseInv]
  | cons i w ih =>
      simp [wordPhaseInv, modularPhaseInv_add, ih, mul_assoc, mul_left_comm]

theorem modularPhase_prime_power (p k : ℕ) (t : ℝ) :
    modularPhase (p ^ k) t = modularPhase p ((k : ℝ) * t) := by
  simp only [modularPhase]
  have hpow : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by norm_num
  rw [hpow]
  rw [Real.log_pow]
  push_cast
  ring_nf

theorem modularPhaseInv_prime_power (p k : ℕ) (t : ℝ) :
    modularPhaseInv (p ^ k) t = modularPhaseInv p ((k : ℝ) * t) := by
  simp only [modularPhaseInv]
  have hpow : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by norm_num
  rw [hpow]
  rw [Real.log_pow]
  push_cast
  ring_nf

theorem sigma_cuntzWordShift (w : List (Fin n)) :
    sigma n primes t (cuntzWordShift w) =
      wordPhase primes t w • cuntzWordShift w := by
  induction w with
  | nil => simp [cuntzWordShift, wordPhase]
  | cons i w ih =>
      simp [cuntzWordShift, map_mul, sigma_cuntzS, ih, wordPhase,
        smul_smul, mul_comm]

theorem sigma_cuntzWordShiftDag (w : List (Fin n)) :
    sigma n primes t (cuntzWordShiftDag w) =
      wordPhaseInv primes t w • cuntzWordShiftDag w := by
  induction w with
  | nil => simp [cuntzWordShiftDag, wordPhaseInv]
  | cons i w ih =>
      simp [cuntzWordShiftDag, map_mul, sigma_cuntzSdag, ih, wordPhaseInv,
        smul_smul]

theorem sigma_cuntzWordShift_append (w₁ w₂ : List (Fin n)) :
    sigma n primes t (cuntzWordShift (w₁ ++ w₂)) =
      sigma n primes t (cuntzWordShift w₁) *
        sigma n primes t (cuntzWordShift w₂) := by
  rw [cuntzWordShift_append, map_mul]

theorem sigma_cuntzWordShift_add (w : List (Fin n)) (s : ℝ) :
    sigma n primes (t + s) (cuntzWordShift w) =
      (sigma n primes t).comp (sigma n primes s) (cuntzWordShift w) := by
  rw [sigma_cuntzWordShift, wordPhase_add]
  simp only [AlgHom.comp_apply]
  rw [sigma_cuntzWordShift, map_smul, sigma_cuntzWordShift]
  simp [smul_smul, mul_comm]

@[simp] theorem sigma_cylinderProjection (w : List (Fin n)) :
    sigma n primes t (cylinderProjection w) = cylinderProjection w := by
  unfold cylinderProjection
  rw [map_mul, sigma_cuntzWordShift, sigma_cuntzWordShiftDag, smul_mul_smul]
  have hprod :
      wordPhase primes t w * wordPhaseInv primes t w = 1 := by
    induction w with
    | nil => simp [wordPhase, wordPhaseInv]
    | cons i w ih =>
        rw [wordPhase, wordPhaseInv]
        calc
          modularPhase (primes i) t * wordPhase primes t w *
                (modularPhaseInv (primes i) t * wordPhaseInv primes t w) =
              (modularPhase (primes i) t * modularPhaseInv (primes i) t) *
                (wordPhase primes t w * wordPhaseInv primes t w) := by ring
          _ = 1 := by rw [← mul_assoc, modularPhase_mul_inv, one_mul, ih]
  rw [hprod, one_smul]

theorem expectation_sigma_comm (x : CuntzAlg n) :
    expectation n (sigma n primes t x) =
      sigma n primes t (expectation n x) := by
  change (∑ i : Fin n,
      (cuntzS n i * cuntzSdag n i) * sigma n primes t x *
        (cuntzS n i * cuntzSdag n i)) =
    sigma n primes t (∑ i : Fin n,
      (cuntzS n i * cuntzSdag n i) * x *
        (cuntzS n i * cuntzSdag n i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, sigma_fixes_projector]

theorem expectation_sigma_cylinderProjection (w : List (Fin n)) :
    expectation n (sigma n primes t (cylinderProjection w)) =
      cylinderProjection w := by
  rw [sigma_cylinderProjection, expectation_cylinderProjection_fixed]

end InfoGeometry.Algebra.CuntzModularTreeFlowBridge
