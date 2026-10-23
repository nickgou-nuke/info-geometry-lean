/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Drazin
import Mathlib.Tactic

/-!
# Arbitrary-index Drazin regularization

Reuse the canonical inverse predicate, core, and spectral projectors. The
witness exponent is not assumed minimal. All results hold in a ring: no
orthogonality, determinant-one claim, or Hilbert-space structure is assumed.
-/

namespace InfoGeometry.Canonical.DrazinRegularization

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {R : Type*} [Ring R] {a d : R} {k : ℕ}

lemma projection_mul_inverse (h : IsDrazinInverse a d k) :
    projection a d * d = d := by
  change a * d * d = d
  rw [h.comm, h.idempotent]

lemma inverse_mul_projection (h : IsDrazinInverse a d k) :
    d * projection a d = d := by
  change d * (a * d) = d
  simpa only [mul_assoc] using h.idempotent

lemma complement_mul_inverse (h : IsDrazinInverse a d k) :
    complementaryProjection a d * d = 0 := by
  rw [complementaryProjection, sub_mul, one_mul, projection_mul_inverse h, sub_self]

lemma inverse_mul_complement (h : IsDrazinInverse a d k) :
    d * complementaryProjection a d = 0 := by
  rw [complementaryProjection, mul_sub, mul_one, inverse_mul_projection h, sub_self]

lemma core_mul_inverse (h : IsDrazinInverse a d k) :
    core a d * d = projection a d := by
  rw [core_eq_mul_projection, mul_assoc, projection_mul_inverse h]
  rfl

lemma inverse_mul_core (h : IsDrazinInverse a d k) :
    d * core a d = projection a d := by
  rw [core_eq_mul_projection, ← mul_assoc, ← h.comm]
  exact projection_is_idempotent h

lemma core_mul_complement (h : IsDrazinInverse a d k) :
    core a d * complementaryProjection a d = 0 := by
  rw [core_eq_mul_projection, mul_assoc, projection_mul_complementaryProjection h, mul_zero]

lemma complement_mul_core (h : IsDrazinInverse a d k) :
    complementaryProjection a d * core a d = 0 := by
  rw [core_eq_mul_projection, ← mul_assoc, complementaryProjection_comm_self h,
    mul_assoc, complementaryProjection_mul_projection h, mul_zero]

/-- Replace the nilpotent operator by identity on its algebraic summand. -/
theorem regularization_inverse (h : IsDrazinInverse a d k) :
    (core a d + complementaryProjection a d) * (d + complementaryProjection a d) = 1 ∧
    (d + complementaryProjection a d) * (core a d + complementaryProjection a d) = 1 := by
  constructor
  · simp only [add_mul, mul_add, core_mul_inverse h, core_mul_complement h,
      complement_mul_inverse h, complementaryProjection_is_idempotent h,
      add_zero, zero_add, projection_add_complementaryProjection]
  · simp only [add_mul, mul_add, inverse_mul_core h, inverse_mul_complement h,
      complement_mul_core h, complementaryProjection_is_idempotent h,
      add_zero, zero_add, projection_add_complementaryProjection]

/-- A native unit, not just a predicate asserting an unspecified inverse. -/
def regularizedUnit (h : IsDrazinInverse a d k) : Rˣ where
  val := core a d + complementaryProjection a d
  inv := d + complementaryProjection a d
  val_inv := (regularization_inverse h).1
  inv_val := (regularization_inverse h).2

/-- The exponent-zero case has no nilpotent summand. -/
theorem index_zero_complement (h : IsDrazinInverse a d 0) :
    complementaryProjection a d = 0 := by
  have he : projection a d = 1 := by simpa [projection] using h.power
  simp [complementaryProjection, he]

theorem index_zero_nilpotent (h : IsDrazinInverse a d 0) : nilpotent a d = 0 := by
  rw [nilpotent_eq_mul_complementaryProjection, index_zero_complement h, mul_zero]

section Scaling
variable [Algebra ℝ R]

/-- Nonzero constant scalar transport of the actual Drazin equations. -/
theorem drazin_smul (h : IsDrazinInverse a d k) {c : ℝ} (hc : c ≠ 0) :
    IsDrazinInverse (c • a) (c⁻¹ • d) k := by
  have hprod (x y : R) : (c • x) * (c⁻¹ • y) = x * y := by
    simp [smul_mul_assoc, mul_smul_comm, smul_smul, hc]
  have hprod' (x y : R) : (c⁻¹ • x) * (c • y) = x * y := by
    simp [smul_mul_assoc, mul_smul_comm, smul_smul, hc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hprod, hprod', h.comm]
  · rw [hprod', mul_smul_comm, h.idempotent]
  · calc
      (c • a) ^ (k + 1) * (c⁻¹ • d) =
          (c ^ (k + 1) * c⁻¹) • (a ^ (k + 1) * d) := by
            rw [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = c ^ k • a ^ k := by
        rw [h.power]
        congr 1
        rw [pow_succ, mul_assoc, mul_inv_cancel₀ hc, mul_one]
      _ = (c • a) ^ k := (smul_pow c a k).symm

/-- Spectral projectors have degree zero under global scalar rescaling. -/
theorem spectral_scale_invariance (a d : R) {c : ℝ} (hc : c ≠ 0) :
    projection (c • a) (c⁻¹ • d) = projection a d ∧
    complementaryProjection (c • a) (c⁻¹ • d) = complementaryProjection a d := by
  have he : projection (c • a) (c⁻¹ • d) = projection a d := by
    simp [projection, smul_mul_assoc, mul_smul_comm, smul_smul, hc]
  exact ⟨he, by simp only [complementaryProjection, he]⟩

end Scaling
end InfoGeometry.Canonical.DrazinRegularization
