/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealPositiveOperatorScaling
import InfoGeometry.Canonical.RealLieJordanGap

/-!
# Quadratic scaling of real matrix and Lie--Jordan operators

Scaling the actual matrix seed scales both its vector Gram operator and its
matrix-space generator quadratically. Nonzero scaling preserves their full
kernels and the seed's noncommutation with its transpose. A nonzero active
element rules out a common positive coercivity constant over all positive
seed rescalings, separately on each carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealLieJordanScaling

open scoped InnerProductSpace Matrix
open Core.LieJordanGenerators RealLieJordanGap RealLieJordanGeometry
open Analysis.RealPositiveOperatorScaling

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Gram matrix is quadratic in the actual matrix seed. -/
theorem gram_smul (u : Matrix n n ℝ) (r : ℝ) :
    (r • u) * (r • u)ᵀ + (r • u)ᵀ * (r • u) =
      (r * r) • (u * uᵀ + uᵀ * u) := by
  simp only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]

/-- Nonzero rescaling preserves noncommutation on the full matrix algebra. -/
theorem smul_mul_transpose_ne_transpose_mul {u : Matrix n n ℝ}
    (hu : u * uᵀ ≠ uᵀ * u) {r : ℝ} (hr : r ≠ 0) :
    (r • u) * (r • u)ᵀ ≠ (r • u)ᵀ * (r • u) := by
  intro h
  have hzero : (r * r) • (u * uᵀ - uᵀ * u) = 0 := by
    simpa only [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_sub] using sub_eq_zero.mpr h
  exact hu (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left (mul_ne_zero hr hr)))

section VectorOperator

/-- Quadratic scaling is preserved by the native matrix-to-vector map. -/
theorem gram_toEuclideanLin_smul (u : Matrix n n ℝ) (r : ℝ) :
    ((r • u) * (r • u)ᵀ + (r • u)ᵀ * (r • u)).toEuclideanLin =
      (r * r) • (u * uᵀ + uᵀ * u).toEuclideanLin := by
  rw [gram_smul, map_smul]

theorem ker_gram_smul (u : Matrix n n ℝ) {r : ℝ} (hr : r ≠ 0) :
    ((r • u) * (r • u)ᵀ + (r • u)ᵀ * (r • u)).toEuclideanLin.ker =
      (u * uᵀ + uᵀ * u).toEuclideanLin.ker := by
  rw [gram_toEuclideanLin_smul, ker_quadratic_smul _ hr]

/-- No single positive vector-space bound works for all positive seed rescalings. -/
theorem gram_not_exists_uniform_positive_bound (u : Matrix n n ℝ)
    (hactive : ∃ x : EuclideanSpace ℝ n,
      x ∈ (u * uᵀ + uᵀ * u).toEuclideanLin.kerᗮ ∧ x ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ ((r • u) * (r • u)ᵀ + (r • u)ᵀ * (r • u)).toEuclideanLin.kerᗮ,
        c * ‖x‖ ^ 2 ≤ inner ℝ x
          (((r • u) * (r • u)ᵀ + (r • u)ᵀ * (r • u)).toEuclideanLin x) := by
  simpa only [gram_toEuclideanLin_smul] using
    not_exists_uniform_positive_coercive_bound _ (gram_toEuclideanLin_isPositive u) hactive

end VectorOperator

section MatrixOperator

open scoped InfoGeometry.Canonical.RealLieJordanGeometry

/-- The generator scales quadratically as an endomorphism of the full matrix space. -/
theorem symmetricGenerator_smul (u : Matrix n n ℝ) (r : ℝ) :
    symmetricGenerator (R := ℝ) (r • u) (r • u)ᵀ =
      (r * r) • symmetricGenerator (R := ℝ) u uᵀ := by
  simp only [symmetricGenerator, Matrix.transpose_smul, map_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_neg]

theorem neg_symmetricGenerator_smul (u : Matrix n n ℝ) (r : ℝ) :
    -symmetricGenerator (R := ℝ) (r • u) (r • u)ᵀ =
      (r * r) • (-symmetricGenerator (R := ℝ) u uᵀ) := by
  rw [symmetricGenerator_smul, smul_neg]

/-- The native stationary algebra is unchanged under nonzero seed rescaling. -/
theorem centralizer_smul (u : Matrix n n ℝ) {r : ℝ} (hr : r ≠ 0) :
    (Subalgebra.centralizer ℝ ({r • u, (r • u)ᵀ} : Set (Matrix n n ℝ))).toSubmodule =
      (Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmodule := by
  rw [← ker_neg_symmetricGenerator, ← ker_neg_symmetricGenerator,
    neg_symmetricGenerator_smul, ker_quadratic_smul _ hr]

/-- No common positive bound works on all scaled common-centralizer complements. -/
theorem generator_not_exists_uniform_positive_bound (u : Matrix n n ℝ)
    (hactive : ∃ x : Matrix n n ℝ,
      x ∈ (Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmoduleᗮ ∧
        x ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ (Subalgebra.centralizer ℝ
          ({r • u, (r • u)ᵀ} : Set (Matrix n n ℝ))).toSubmoduleᗮ,
        c * ‖x‖ ^ 2 ≤ inner ℝ x
          ((-symmetricGenerator (R := ℝ) (r • u) (r • u)ᵀ) x) := by
  have ha : ∃ x : Matrix n n ℝ,
      x ∈ (-symmetricGenerator (R := ℝ) u uᵀ).kerᗮ ∧ x ≠ 0 := by
    simpa only [ker_neg_symmetricGenerator] using hactive
  have h := not_exists_uniform_positive_coercive_bound _
    (neg_symmetricGenerator_isPositive u) ha
  simpa only [← neg_symmetricGenerator_smul, ker_neg_symmetricGenerator] using h

end MatrixOperator

end InfoGeometry.Canonical.RealLieJordanScaling
