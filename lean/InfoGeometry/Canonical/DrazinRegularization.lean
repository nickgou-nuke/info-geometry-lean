/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.MoorePenrose

/-!
# Arbitrary-index Drazin core regularization

Contract: in an arbitrary unital ring, a canonical witness `IsDrazinInverse a d k`
gives mutually inverse elements `core a d + Q` and `d + Q`, where the existing
`complementaryProjection a d` is `Q`. No restriction on `k` is imposed.
The input is a witness, not a claim of existence for every ring element.
The projector identities and core definition come from `Canonical.Drazin`.
This does not assert that `a + Q` has inverse `d + Q` at arbitrary index.

The final lemmas rescale the existing canonical Drazin and singular
Moore--Penrose witness predicates in real algebras by a nonzero scalar.
-/

namespace InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {R : Type*} [Ring R] {a d : R} {k : ℕ}

/-- The regular projector acts as the identity on the inverse witness. -/
theorem projection_mul_inverse (h : IsDrazinInverse a d k) :
    projection a d * d = d := by
  change (a * d) * d = d
  rw [h.comm, h.idempotent]

/-- The inverse witness vanishes on the complementary block. -/
theorem inverse_mul_complementaryProjection (h : IsDrazinInverse a d k) :
    d * complementaryProjection a d = 0 := by
  change d * (1 - a * d) = 0
  rw [mul_sub, mul_one, ← mul_assoc, h.idempotent, sub_self]

/-- The complementary block vanishes on the inverse witness. -/
theorem complementaryProjection_mul_inverse (h : IsDrazinInverse a d k) :
    complementaryProjection a d * d = 0 := by
  rw [complementaryProjection, sub_mul, one_mul, projection_mul_inverse h, sub_self]

/-- The core and its inverse multiply to the regular projector. -/
theorem core_mul_inverse_eq_projection (h : IsDrazinInverse a d k) :
    core a d * d = projection a d := by
  calc
    core a d * d = a * (projection a d * d) := by
      rw [core_eq_mul_projection, mul_assoc]
    _ = a * d := by rw [projection_mul_inverse h]
    _ = projection a d := rfl

/-- The reverse core/inverse product is the same projector. -/
theorem inverse_mul_core_eq_projection (h : IsDrazinInverse a d k) :
    d * core a d = projection a d := by
  rw [core_eq_mul_projection, ← mul_assoc, ← h.comm]
  exact projection_is_idempotent h

/-- The core annihilates the complementary projector. -/
theorem core_mul_complementaryProjection (h : IsDrazinInverse a d k) :
    core a d * complementaryProjection a d = 0 := by
  rw [core_eq_mul_projection, mul_assoc, projection_mul_complementaryProjection h,
    mul_zero]

/-- The complementary projector annihilates the core. -/
theorem complementaryProjection_mul_core (h : IsDrazinInverse a d k) :
    complementaryProjection a d * core a d = 0 := by
  rw [core_eq_mul_projection, ← mul_assoc, complementaryProjection_comm_self h,
    mul_assoc, complementaryProjection_mul_projection h, mul_zero]

/-- Filling the complementary block with identity makes the core invertible. -/
theorem core_add_complementaryProjection_mul_inverse
    (h : IsDrazinInverse a d k) :
    (core a d + complementaryProjection a d) *
      (d + complementaryProjection a d) = 1 := by
  rw [add_mul, mul_add, mul_add, core_mul_inverse_eq_projection h,
    core_mul_complementaryProjection h, complementaryProjection_mul_inverse h,
    complementaryProjection_is_idempotent h, add_zero, zero_add]
  exact projection_add_complementaryProjection

/-- The regularized inverse is also a left inverse, at every Drazin index. -/
theorem inverse_mul_core_add_complementaryProjection
    (h : IsDrazinInverse a d k) :
    (d + complementaryProjection a d) *
      (core a d + complementaryProjection a d) = 1 := by
  rw [add_mul, mul_add, mul_add, inverse_mul_core_eq_projection h,
    inverse_mul_complementaryProjection h, complementaryProjection_mul_core h,
    complementaryProjection_is_idempotent h, add_zero, zero_add]
  exact projection_add_complementaryProjection

/-- Nonzero real rescaling preserves the Drazin index of a witness. -/
theorem rescale [Algebra ℝ R] (h : IsDrazinInverse a d k)
    {c : ℝ} (hc : c ≠ 0) :
    IsDrazinInverse (c • a) (c⁻¹ • d) k := by
  refine mk ?_ ?_ ?_
  · simpa [smul_mul_smul_comm, hc] using h.comm
  · simpa [smul_mul_smul_comm, hc] using
      congrArg (fun x : R => c⁻¹ • x) h.idempotent
  · rw [smul_pow, smul_mul_smul_comm, h.power, smul_pow]
    have hscalar : c ^ (k + 1) * c⁻¹ = c ^ k := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hscalar]

end InfoGeometry.Canonical.Drazin.IsDrazinInverse

namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

/-- Reciprocal rescaling preserves all four Penrose equations.
No star/scalar compatibility is needed because both products are unchanged. -/
theorem rescale {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R]
    {a d : R} (h : IsMoorePenroseInverse a d) {c : ℝ} (hc : c ≠ 0) :
    IsMoorePenroseInverse (c • a) (c⁻¹ • d) := by
  have had : (c • a) * (c⁻¹ • d) = a * d := by
    simp [hc]
  have hda : (c⁻¹ • d) * (c • a) = d * a := by
    simp [hc]
  refine mk ?_ ?_ ?_ ?_
  · rw [had, mul_smul_comm, h.aba_eq_a]
  · rw [hda, mul_smul_comm, h.bab_eq_b]
  · rw [had]
    exact h.ab_adj_eq
  · rw [hda]
    exact h.ba_adj_eq

end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
