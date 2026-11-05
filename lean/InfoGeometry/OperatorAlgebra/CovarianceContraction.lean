/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceDynamics
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contractive operator covariance dynamics

In a normed star ring with isometric adjoint, the full affine covariance map
has Lipschitz constant `‖T‖₊ ^ 2`. Completeness and `‖T‖ < 1` then give an actual
unique fixed point and convergence of all iterates by Mathlib's contraction
theorem. No commutation or nilpotence is required in this analytic result.

The norm is assumed to be a submultiplicative ring norm. This file does not
identify it with any arbitrary entrywise matrix norm, infer positivity on an
unordered star ring, or prove convergence of a state-dependent transition.
-/

namespace InfoGeometry.OperatorAlgebra.CovarianceContraction

open Filter
open scoped Topology NNReal
open InfoGeometry.OperatorAlgebra.CovarianceTransport

variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A]

/-- The bound controls the norm of the full covariance difference. -/
theorem norm_covarianceStep_sub_le (T Q C D : A) :
    ‖covarianceStep T Q C - covarianceStep T Q D‖ ≤ ‖T‖ ^ 2 * ‖C - D‖ := by
  rw [covarianceStep_sub]
  calc
    ‖T * (C - D) * star T‖ ≤ ‖T * (C - D)‖ * ‖star T‖ := norm_mul_le _ _
    _ ≤ (‖T‖ * ‖C - D‖) * ‖star T‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖T‖ ^ 2 * ‖C - D‖ := by rw [norm_star]; ring

theorem covarianceStep_lipschitz (T Q : A) :
    LipschitzWith (‖T‖₊ ^ 2) (covarianceStep T Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro C D
  simpa only [dist_eq_norm, NNReal.coe_pow, coe_nnnorm] using
    norm_covarianceStep_sub_le T Q C D

/-- A strict transition norm bound makes the affine map a contraction. -/
theorem covarianceStep_contracting (T Q : A) (hT : ‖T‖ < 1) :
    ContractingWith (‖T‖₊ ^ 2) (covarianceStep T Q) := by
  refine ⟨?_, covarianceStep_lipschitz T Q⟩
  have h : ‖T‖ ^ 2 < 1 := (sq_lt_one_iff₀ (norm_nonneg T)).2 hT
  exact_mod_cast h

/-- Stationary uniqueness needs no completeness assumption. -/
theorem stationary_unique_of_norm_lt_one (T Q : A) (hT : ‖T‖ < 1)
    {C D : A} (hC : covarianceStep T Q C = C) (hD : covarianceStep T Q D = D) :
    C = D :=
  (covarianceStep_contracting T Q hT).fixedPoint_unique' hC hD

variable [CompleteSpace A]

/-- Completeness supplies a stationary operator; it is not assumed as input. -/
theorem existsUnique_stationary_of_norm_lt_one (T Q : A) (hT : ‖T‖ < 1) :
    ∃! C : A, covarianceStep T Q C = C := by
  let h := covarianceStep_contracting T Q hT
  exact ⟨ContractingWith.fixedPoint (covarianceStep T Q) h,
    h.fixedPoint_isFixedPt, fun _ hC => h.fixedPoint_unique hC⟩

/-- Every initial operator converges to the constructed stationary operator. -/
theorem exists_stationary_and_tendsto (T Q : A) (hT : ‖T‖ < 1) :
    ∃ S : A, covarianceStep T Q S = S ∧
      ∀ C : A, Tendsto (fun k : ℕ => (covarianceStep T Q)^[k] C) atTop (𝓝 S) := by
  let h := covarianceStep_contracting T Q hT
  exact ⟨ContractingWith.fixedPoint (covarianceStep T Q) h,
    h.fixedPoint_isFixedPt, fun C => h.tendsto_iterate_fixedPoint C⟩

/-- A quantified finite-time error bound around the native Banach fixed point. -/
theorem norm_iterate_sub_fixedPoint_le (T Q C : A) (hT : ‖T‖ < 1) (k : ℕ) :
    ‖(covarianceStep T Q)^[k] C -
      ContractingWith.fixedPoint (covarianceStep T Q) (covarianceStep_contracting T Q hT)‖ ≤
      ‖C - covarianceStep T Q C‖ * (‖T‖ ^ 2) ^ k / (1 - ‖T‖ ^ 2) := by
  simpa only [dist_eq_norm, NNReal.coe_pow, coe_nnnorm] using
    (covarianceStep_contracting T Q hT).apriori_dist_iterate_fixedPoint_le C k

end InfoGeometry.OperatorAlgebra.CovarianceContraction
