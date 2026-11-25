/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import GaussianBlockSpin.ReflectionPositiveCovariance
import GaussianBlockSpin.WeightedCoarseGraining

/-!
# Reflected positivity of the weighted coarse covariance

This adapter applies the standalone covariance transport theorem to the actual
Schur-complement precision owner. Ordinary positive definiteness supplies the
Woodbury identity. Reflection positivity remains an explicit, separate
hypothesis for the fine covariance and the coarse noise.
-/

noncomputable section

open Matrix

namespace GaussianBlockSpin.WeightedCoarseGraining

variable {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p] [Finite q]
variable [DecidableEq n] [DecidableEq m]

/-- The inverse of the actual weighted Schur-complement precision has a
positive reflected form on the selected coarse tests, provided the fine
covariance and the noise separately have positive reflected forms and the
blocking map preserves reflection and the selected test spaces. -/
theorem coarsePrecision_inv_reflection_posSemidef
    (A : Matrix n n ℝ) (R : Matrix m m ℝ) (Q : Matrix m n ℝ)
    (θf : Matrix n n ℝ) (θc : Matrix m m ℝ)
    (Uf : Matrix n p ℝ) (Uc : Matrix m q ℝ) (B : Matrix p q ℝ)
    (hA : A.PosDef) (hR : R.PosDef)
    (hReflection : θc * Q = Q * θf)
    (hTests : Qᵀ * Uc = Uf * B)
    (hFine : (Ufᵀ * θf * A⁻¹ * Uf).PosSemidef)
    (hNoise : (Ucᵀ * θc * R⁻¹ * Uc).PosSemidef) :
    (Ucᵀ * θc * (coarsePrecision A R Q)⁻¹ * Uc).PosSemidef := by
  rw [coarsePrecision_inv Q hA hR, conjTranspose_eq_transpose_of_trivial]
  exact ReflectionPositiveCovariance.reflected_covariance_posSemidef
    θf θc A⁻¹ R⁻¹ Q Uf Uc B hReflection hTests hFine hNoise

end GaussianBlockSpin.WeightedCoarseGraining
