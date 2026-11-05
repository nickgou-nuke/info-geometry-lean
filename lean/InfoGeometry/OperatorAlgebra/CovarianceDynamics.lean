/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceTransport
import InfoGeometry.Canonical.FiniteSteinInverse

/-!
# Finite noncommutative covariance dynamics

The affine recurrence `C ↦ T * C * star T + Q` has an exact finite-time
formula. Its accumulated noise is the existing `finiteStein` construction.
Products retain their order throughout; the transition, initial covariance,
and noise covariance need not commute.

Nilpotence of the transition gives an explicit stationary covariance, uniqueness
among all ambient operators, and exact loss of the initial state after finitely
many updates. Positivity is established on native finite matrices over an
`RCLike` field. No analytic convergence, large-dimension limit, or stochastic
closure error estimate is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.CovarianceDynamics

open InfoGeometry.Canonical.FiniteSteinInverse
open InfoGeometry.OperatorAlgebra.CovarianceTransport

variable {A : Type*} [Ring A] [StarRing A]

/-- The exact finite-time formula retains the transported initial covariance. -/
theorem covariance_iterate_eq (T Q C : A) (k : ℕ) :
    (covarianceStep T Q)^[k] C =
      T ^ k * C * star (T ^ k) + finiteStein T (star T) Q k := by
  induction k generalizing C with
  | zero => simp [finiteStein]
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      have hpow :
          T ^ k * (T * C * star T) * star (T ^ k) =
            T ^ (k + 1) * C * star (T ^ (k + 1)) := by
        simp only [pow_succ, star_mul, mul_assoc]
      have hsum :
          finiteStein T (star T) Q (k + 1) =
            finiteStein T (star T) Q k + T ^ k * Q * star (T ^ k) := by
        simp only [finiteStein, Finset.sum_range_succ, star_pow]
      simp only [covarianceStep, mul_add, add_mul]
      rw [hpow, hsum]
      abel

/-- The same innovation cancels when comparing two initial covariances. -/
theorem covariance_iterate_sub (T Q C D : A) (k : ℕ) :
    (covarianceStep T Q)^[k] C - (covarianceStep T Q)^[k] D =
      T ^ k * (C - D) * star (T ^ k) := by
  rw [covariance_iterate_eq, covariance_iterate_eq]
  noncomm_ring

/-- Error relative to a supplied fixed point is transported by ordered powers. -/
theorem covariance_iterate_sub_fixed (T Q C S : A)
    (hS : covarianceStep T Q S = S) (k : ℕ) :
    (covarianceStep T Q)^[k] C - S =
      T ^ k * (C - S) * star (T ^ k) := by
  simpa only [Function.iterate_fixed hS] using covariance_iterate_sub T Q C S k

/-- Affine fixed points are exactly solutions of the existing Stein equation. -/
theorem covarianceStep_eq_self_iff (T Q C : A) :
    covarianceStep T Q C = C ↔ C - T * C * star T = Q := by
  unfold covarianceStep
  constructor
  · intro h
    exact (sub_eq_iff_eq_add').2 h.symm
  · intro h
    exact ((sub_eq_iff_eq_add').1 h).symm

/-- Nilpotence removes the initial covariance term exactly. -/
theorem covariance_iterate_eq_finiteStein_of_nilpotent (T Q C : A)
    (k : ℕ) (hT : T ^ k = 0) :
    (covarianceStep T Q)^[k] C = finiteStein T (star T) Q k := by
  rw [covariance_iterate_eq, hT]
  simp only [zero_mul, zero_add]

/-- Every later finite time has the same value; no limit passage is needed. -/
theorem covariance_iterate_add_eq_finiteStein_of_nilpotent (T Q C : A)
    (k l : ℕ) (hT : T ^ k = 0) :
    (covarianceStep T Q)^[k + l] C = finiteStein T (star T) Q k := by
  rw [Function.iterate_add_apply]
  exact covariance_iterate_eq_finiteStein_of_nilpotent T Q _ k hT

/-- The repository's finite Stein inverse constructs a stationary covariance. -/
theorem finiteStein_fixed_of_nilpotent (T Q : A) (k : ℕ) (hT : T ^ k = 0) :
    covarianceStep T Q (finiteStein T (star T) Q k) =
      finiteStein T (star T) Q k := by
  apply (covarianceStep_eq_self_iff T Q _).2
  exact solve_of_left_nilpotent T (star T) Q k hT

/-- The nilpotent stationary covariance is unique among all operators. -/
theorem stationary_covariance_unique (T Q C D : A) (k : ℕ) (hT : T ^ k = 0)
    (hC : covarianceStep T Q C = C) (hD : covarianceStep T Q D = D) : C = D := by
  exact solution_unique T (star T) Q C D k hT
    ((covarianceStep_eq_self_iff T Q C).1 hC)
    ((covarianceStep_eq_self_iff T Q D).1 hD)

/-- Every fixed point is the explicitly constructed finite Stein sum. -/
theorem stationary_covariance_eq_finiteStein (T Q C : A)
    (k : ℕ) (hT : T ^ k = 0) (hC : covarianceStep T Q C = C) :
    C = finiteStein T (star T) Q k := by
  exact stationary_covariance_unique T Q C _ k hT hC
    (finiteStein_fixed_of_nilpotent T Q k hT)

/-- Star acts on the noise argument while preserving the ordered Gramian sum. -/
theorem finiteStein_star (T Q : A) (k : ℕ) :
    star (finiteStein T (star T) Q k) =
      finiteStein T (star T) (star Q) k := by
  simp only [finiteStein, star_sum, star_mul, star_pow, star_star, mul_assoc]

/-- Self-adjoint noise gives a self-adjoint accumulated covariance. -/
theorem finiteStein_selfAdjoint (T Q : A) (hQ : star Q = Q) (k : ℕ) :
    star (finiteStein T (star T) Q k) = finiteStein T (star T) Q k := by
  rw [finiteStein_star, hQ]

section Matrices

open Matrix
open scoped ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Every summand transports the full positive noise operator by congruence. -/
theorem finiteStein_posSemidef (T : Matrix n n 𝕜) {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (k : ℕ) :
    (finiteStein T (star T) Q k).PosSemidef := by
  induction k with
  | zero => simpa [finiteStein] using (Matrix.PosSemidef.zero : (0 : Matrix n n 𝕜).PosSemidef)
  | succ k ih =>
      rw [finiteStein, Finset.sum_range_succ]
      exact ih.add (by
        simpa only [← Matrix.star_eq_conjTranspose, star_pow] using
          hQ.mul_mul_conjTranspose_same (T ^ k))

/-- Positive initial and innovation covariances stay positive at every finite time. -/
theorem covariance_iterate_posSemidef (T : Matrix n n 𝕜) {Q C : Matrix n n 𝕜}
    (hC : C.PosSemidef) (hQ : Q.PosSemidef) (k : ℕ) :
    ((covarianceStep T Q)^[k] C).PosSemidef := by
  induction k with
  | zero => exact hC
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact covarianceStep_posSemidef T ih hQ

/-- Positivity of the initial covariance difference is preserved for all finite times. -/
theorem covariance_iterate_sub_posSemidef (T Q : Matrix n n 𝕜)
    {C D : Matrix n n 𝕜} (hCD : (C - D).PosSemidef) (k : ℕ) :
    ((covarianceStep T Q)^[k] C - (covarianceStep T Q)^[k] D).PosSemidef := by
  rw [covariance_iterate_sub]
  simpa only [Matrix.star_eq_conjTranspose] using
    hCD.mul_mul_conjTranspose_same (T ^ k)

/-- Positive noise and a nilpotent transition have one positive stationary covariance. -/
theorem existsUnique_stationary_covariance (T : Matrix n n 𝕜) {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (k : ℕ) (hT : T ^ k = 0) :
    ∃! C : Matrix n n 𝕜, C.PosSemidef ∧ covarianceStep T Q C = C := by
  refine ⟨finiteStein T (star T) Q k,
    ⟨finiteStein_posSemidef T hQ k, finiteStein_fixed_of_nilpotent T Q k hT⟩, ?_⟩
  intro C hC
  exact stationary_covariance_eq_finiteStein T Q C k hT hC.2

end Matrices

end InfoGeometry.OperatorAlgebra.CovarianceDynamics
