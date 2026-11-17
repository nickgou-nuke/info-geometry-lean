/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealMetricAdjoint
import InfoGeometry.CliffordWeyl.DiracMetricCovariance
import Mathlib.Tactic.NoncommRing

/-!
# Inverse congruence in the existing real weighted-adjoint interface

The moving weight is the actual unit `star g⁻¹ * w * g⁻¹`. The matrix
covariance theorem is reused from `DiracMetricCovariance`; the new bridges
identify its adjoint with the existing weighted adjoint and its preserved
pairing with native `Matrix.toBilin'`.

The relative moving weight is the inverse of `g * adjoint w g`, with this
order essential. It is not identified with `adjoint w g * g`. Orthogonality
is sufficient to preserve an involutive metric under inverse congruence;
an arbitrary invertible change of basis need not do so.
-/

namespace InfoGeometry.OperatorAlgebra.RealMetricTransport

open Matrix WeightedAdjointCompatibility
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native weighted adjoint is covariant when both the operator and the
metric are transported. No symmetry or positivity premise is needed. -/
theorem weightedAdjoint_inverse_congruence
    (w g : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    adjoint (star g⁻¹ * w * g⁻¹)
        ((g : Matrix n n ℝ) * A * (↑g⁻¹ : Matrix n n ℝ)) =
      (g : Matrix n n ℝ) * adjoint w A * (↑g⁻¹ : Matrix n n ℝ) := by
  simpa only [adjoint, mul_inv_rev, inv_inv, Units.val_mul,
    Units.coe_star_inv, Units.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, mul_assoc] using
    (metric_adjoint_change_basis (g : Matrix n n ℝ) (↑g⁻¹ : Matrix n n ℝ)
      (w : Matrix n n ℝ) (↑w⁻¹ : Matrix n n ℝ) A g.inv_val)

/-- Simultaneous transport of the two vectors and inverse congruence of the
metric preserves the native real bilinear pairing. -/
theorem inverse_congruence_pullback
    (g : (Matrix n n ℝ)ˣ) (η : Matrix n n ℝ) (x y : n → ℝ) :
    ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ)).toBilin'
        ((g : Matrix n n ℝ) *ᵥ x) ((g : Matrix n n ℝ) *ᵥ y) =
      η.toBilin' x y := by
  have hmetric :
      (g : Matrix n n ℝ)ᵀ *
          ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ)) *
            (g : Matrix n n ℝ) = η := by
    calc
      _ = ((↑g⁻¹ : Matrix n n ℝ) * (g : Matrix n n ℝ))ᵀ * η *
          ((↑g⁻¹ : Matrix n n ℝ) * (g : Matrix n n ℝ)) := by
        rw [transpose_mul]
        noncomm_ring
      _ = η := by rw [g.inv_val]; simp
  have hform := congrArg
    (fun B : LinearMap.BilinForm ℝ (n → ℝ) => B x y)
    (Matrix.toBilin'_comp
      ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ))
      (g : Matrix n n ℝ) (g : Matrix n n ℝ))
  rw [hmetric] at hform
  exact hform

/-- The relative moving metric has an ordered two-sided inverse. In general
that inverse is `g * adjoint w g`, not `adjoint w g * g`. -/
theorem relative_inverse_congruence_inverse
    (w g : (Matrix n n ℝ)ˣ) :
    ((g : Matrix n n ℝ) * adjoint w (g : Matrix n n ℝ)) *
        ((↑w⁻¹ : Matrix n n ℝ) *
          (↑(star g⁻¹ * w * g⁻¹) : Matrix n n ℝ)) = 1 ∧
      ((↑w⁻¹ : Matrix n n ℝ) *
          (↑(star g⁻¹ * w * g⁻¹) : Matrix n n ℝ)) *
        ((g : Matrix n n ℝ) * adjoint w (g : Matrix n n ℝ)) = 1 := by
  have hright :
      (g * (w⁻¹ * star g * w)) * (w⁻¹ * (star g⁻¹ * w * g⁻¹)) = 1 := by
    simp [star_inv, mul_assoc]
  have hleft :
      (w⁻¹ * (star g⁻¹ * w * g⁻¹)) * (g * (w⁻¹ * star g * w)) = 1 := by
    simp [star_inv, mul_assoc]
  constructor
  · simpa [adjoint, mul_assoc] using
      congrArg (fun u : (Matrix n n ℝ)ˣ => (u : Matrix n n ℝ)) hright
  · simpa [adjoint, mul_assoc] using
      congrArg (fun u : (Matrix n n ℝ)ˣ => (u : Matrix n n ℝ)) hleft

/-- Orthogonality turns inverse congruence into ordinary orthogonal
conjugation and preserves the square-one normalization of a metric. -/
theorem orthogonal_inverse_congruence_involutive
    (g : (Matrix n n ℝ)ˣ) (η : Matrix n n ℝ)
    (hg : (g : Matrix n n ℝ)ᵀ * (g : Matrix n n ℝ) = 1)
    (hη : η * η = 1) :
    ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ)) =
        (g : Matrix n n ℝ) * η * (g : Matrix n n ℝ)ᵀ ∧
      ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ)) *
        ((↑g⁻¹ : Matrix n n ℝ)ᵀ * η * (↑g⁻¹ : Matrix n n ℝ)) = 1 := by
  have ht : (g : Matrix n n ℝ)ᵀ = (↑g⁻¹ : Matrix n n ℝ) := by
    calc
      _ = ((g : Matrix n n ℝ)ᵀ * (g : Matrix n n ℝ)) *
          (↑g⁻¹ : Matrix n n ℝ) := by simp [mul_assoc]
      _ = (↑g⁻¹ : Matrix n n ℝ) := by rw [hg, one_mul]
  have hit : (↑g⁻¹ : Matrix n n ℝ)ᵀ = (g : Matrix n n ℝ) := by
    rw [← ht, transpose_transpose]
  rw [hit, ht]
  constructor
  · rfl
  · calc
      _ = (g : Matrix n n ℝ) * η *
          ((↑g⁻¹ : Matrix n n ℝ) * (g : Matrix n n ℝ)) * η *
            (↑g⁻¹ : Matrix n n ℝ) := by noncomm_ring
      _ = (g : Matrix n n ℝ) * (η * η) * (↑g⁻¹ : Matrix n n ℝ) := by
        rw [g.inv_val]
        noncomm_ring
      _ = 1 := by rw [hη]; simp

end InfoGeometry.OperatorAlgebra.RealMetricTransport
