/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinRegularization

/-!
# Drazin and Moore-Penrose partition interface

The spectral and metric partitions have different hypotheses. This module
joins their existing owners without identifying oblique and orthogonal
projectors. Selectively adapted from upstream/feat/drazin-mp-sector-partitions;
the existing DrazinRegularization owner retains reciprocal MP transport.
Contract: the two ordered products satisfy only the outer-inverse equation
under the native Drazin and MP witnesses; no new inverse predicate is defined.
Scalar transport is constant global homogeneity, not a local
Weyl connection. DMP products are not inverses on the nilpotent summand.
-/

namespace InfoGeometry.Canonical.DrazinMoorePenrosePartition

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] {a d m : R} {k : ℕ}

/-- The ordered Drazin--Moore--Penrose product. -/
def dmpInverse (a d m : R) : R := d * a * m

/-- The dual ordered product. -/
def dualDmpInverse (a d m : R) : R := m * a * d

theorem dmp_eq_projection_mul (h : IsDrazinInverse a d k) :
    dmpInverse a d m = Drazin.IsDrazinInverse.projection a d * m := by
  unfold dmpInverse Drazin.IsDrazinInverse.projection
  rw [h.comm]

/-- The DMP product satisfies an outer-inverse equation; it is not asserted
here to be the Moore-Penrose or Drazin inverse. -/
theorem dmp_outer_inverse [StarRing R] (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dmpInverse a d m * a * dmpInverse a d m = dmpInverse a d m := by
  unfold dmpInverse
  calc
    (d * a * m) * a * (d * a * m) = d * (a * m * a) * d * a * m := by
      simp only [mul_assoc]
    _ = d * a * m := by rw [hm.aba_eq_a, hd.idempotent]

theorem dualDmp_outer_inverse [StarRing R] (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dualDmpInverse a d m * a * dualDmpInverse a d m = dualDmpInverse a d m := by
  unfold dualDmpInverse
  calc
    (m * a * d) * a * (m * a * d) = m * a * d * (a * m * a) * d := by
      simp only [mul_assoc]
    _ = m * a * (d * a * d) := by rw [hm.aba_eq_a]; simp only [mul_assoc]
    _ = m * a * d := by rw [hd.idempotent]

section Scaling
variable [Algebra ℝ R]

/-- Reciprocal scaling gives degree minus one; no inverse witness is needed. -/
theorem dmp_smul (a d m : R) {c : ℝ} (hc : c ≠ 0) :
    dmpInverse (c • a) (c⁻¹ • d) (c⁻¹ • m) = c⁻¹ • dmpInverse a d m := by
  unfold dmpInverse
  simp [smul_smul, hc]

end Scaling
end InfoGeometry.Canonical.DrazinMoorePenrosePartition
