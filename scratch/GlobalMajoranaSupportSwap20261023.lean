/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DiracSuperalgebra

/-!
# Individual swaps for the native completed Majorana reflection

Uncompiled scratch candidate for the 2026-10-23 compression intake.
Here Pplus is `exactSupport d b = d * b` and Pminus is
`coexactSupport d b = b * d`. The reflection and all carriers are native.
The swaps hold in an arbitrary involutive ring; no cancellation of 2 is used.
Self-adjointness has a separate explicit duality premise.
-/

namespace InfoGeometry.Core.DiracSuperalgebra.SupportSwapCandidate

open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R] {d b : R}

/-- The completed reflection exchanges the forward arrow with its MP inverse. -/
theorem globalMajoranaReflection_conjugates_forward
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    globalMajoranaReflection d b * d * globalMajoranaReflection d b = b := by
  have hleft : globalMajoranaReflection d b * d = b * d := by
    simp only [globalMajoranaReflection, majoranaPlus, add_mul, hd,
      h.harmonicSupport_mul_eq_zero hd, zero_add, add_zero]
  have hdd : b * d * d = 0 := by rw [mul_assoc, hd, mul_zero]
  have hdh : b * d * harmonicSupport d b = 0 := by
    rw [mul_assoc, h.mul_harmonicSupport_eq_zero hd, mul_zero]
  rw [hleft]
  unfold globalMajoranaReflection majoranaPlus
  rw [mul_add, mul_add, hdd, h.bab_eq_b, hdh, zero_add, add_zero]

/-- The reverse exchange follows from the native global involution law. -/
theorem globalMajoranaReflection_conjugates_inverse
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    globalMajoranaReflection d b * b * globalMajoranaReflection d b = d := by
  let W := globalMajoranaReflection d b
  have hsq : W * W = 1 := globalMajoranaReflection_sq h hd
  have hf : W * d * W = b := globalMajoranaReflection_conjugates_forward h hd
  change W * b * W = d
  calc
    W * b * W = W * (W * d * W) * W := by rw [hf]
    _ = (W * W) * d * (W * W) := by simp only [mul_assoc]
    _ = d := by rw [hsq, one_mul, mul_one]

/-- Conjugation exchanges the exact support with the coexact support. -/
theorem globalMajoranaReflection_conjugates_exactSupport
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    globalMajoranaReflection d b * exactSupport d b *
      globalMajoranaReflection d b = coexactSupport d b := by
  let W := globalMajoranaReflection d b
  have hsq : W * W = 1 := globalMajoranaReflection_sq h hd
  have hf : W * d * W = b := globalMajoranaReflection_conjugates_forward h hd
  have hb : W * b * W = d := globalMajoranaReflection_conjugates_inverse h hd
  change W * (d * b) * W = b * d
  calc
    W * (d * b) * W = W * d * (W * W) * b * W := by
      rw [hsq, mul_one]
      simp only [mul_assoc]
    _ = (W * d * W) * (W * b * W) := by simp only [mul_assoc]
    _ = b * d := by rw [hf, hb]

/-- Conjugation exchanges the coexact support with the exact support. -/
theorem globalMajoranaReflection_conjugates_coexactSupport
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    globalMajoranaReflection d b * coexactSupport d b *
      globalMajoranaReflection d b = exactSupport d b := by
  let W := globalMajoranaReflection d b
  have hsq : W * W = 1 := globalMajoranaReflection_sq h hd
  have hf : W * d * W = b := globalMajoranaReflection_conjugates_forward h hd
  have hb : W * b * W = d := globalMajoranaReflection_conjugates_inverse h hd
  change W * (b * d) * W = d * b
  calc
    W * (b * d) * W = W * b * (W * W) * d * W := by
      rw [hsq, mul_one]
      simp only [mul_assoc]
    _ = (W * b * W) * (W * d * W) := by simp only [mul_assoc]
    _ = d * b := by rw [hb, hf]

/-- Self-adjointness requires duality in addition to the MP premise;
square-zero is unnecessary for this identity. -/
theorem globalMajoranaReflection_star
    (h : IsMoorePenroseInverse d b) (hdual : b = star d) :
    star (globalMajoranaReflection d b) = globalMajoranaReflection d b := by
  unfold globalMajoranaReflection
  rw [star_add, (majorana_star_symmetry hdual).1, harmonicSupport_star h]

end InfoGeometry.Core.DiracSuperalgebra.SupportSwapCandidate
