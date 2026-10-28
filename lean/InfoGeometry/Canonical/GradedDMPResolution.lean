/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Canonical.DrazinMoorePenrosePartition

/-!
# Exact graded Drazin--Moore--Penrose recovery

Reuse the existing indexed Drazin predicate, four Penrose equations, ordered
DMP products and division-free Peirce grading. The DMP products are outer
inverses, not generally inner inverses. Their failure to recover the original
operator is exactly its complementary Fitting summand. No commutativity of
the ambient algebra, positivity, or inverse existence is assumed.
-/

namespace InfoGeometry.Canonical.GradedDMPResolution

open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinMoorePenrosePartition
open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] {a d m : R} {k : ℕ}

/-- The right-ordered product is the metric inverse followed by spectral support. -/
theorem dualDmp_eq_mul_projection (a d m : R) :
    dualDmpInverse a d m = m * projection a d := by
  simp only [dualDmpInverse, projection, mul_assoc]

/-- The difference of the two ordered products is a genuine commutator. -/
theorem dmp_difference (hd : IsDrazinInverse a d k) :
    dmpInverse a d m - dualDmpInverse a d m =
      projection a d * m - m * projection a d := by
  rw [dmp_eq_projection_mul hd, dualDmp_eq_mul_projection]

/-- Multiplication by the reflection recovers the full odd part of `m`. -/
theorem odd_inverse_eq_reflection_difference (hd : IsDrazinInverse a d k) :
    oddPart (projection a d) m = reflection (projection a d) *
      (dmpInverse a d m - dualDmpInverse a d m) := by
  rw [dmp_difference hd]
  exact odd_eq_reflection_commutator (projection_is_idempotent hd) m

/-- Equality of DMP and MPD is exactly the absence of odd inverse blocks. -/
theorem dmp_eq_dual_iff_odd_zero (hd : IsDrazinInverse a d k) :
    dmpInverse a d m = dualDmpInverse a d m ↔ oddPart (projection a d) m = 0 := by
  rw [dmp_eq_projection_mul hd, dualDmp_eq_mul_projection]
  exact (odd_zero_iff_commute (projection_is_idempotent hd) m).symm

/-- The nonzero defect, when present, belongs to the odd Peirce component. -/
theorem difference_is_odd (hd : IsDrazinInverse a d k) :
    oddPart (projection a d) (dmpInverse a d m - dualDmpInverse a d m) =
      dmpInverse a d m - dualDmpInverse a d m := by
  rw [dmp_difference hd]
  exact (commutator_is_odd (projection_is_idempotent hd) m).1

theorem difference_anticommutes (hd : IsDrazinInverse a d k) :
    reflection (projection a d) * (dmpInverse a d m - dualDmpInverse a d m) +
      (dmpInverse a d m - dualDmpInverse a d m) * reflection (projection a d) = 0 := by
  rw [dmp_difference hd]
  exact (commutator_is_odd (projection_is_idempotent hd) m).2

/-- Odd feedback returns to the even component; its square need not vanish. -/
theorem difference_square_even (hd : IsDrazinInverse a d k) :
    evenPart (projection a d)
        ((dmpInverse a d m - dualDmpInverse a d m) ^ 2) =
      (dmpInverse a d m - dualDmpInverse a d m) ^ 2 := by
  let x := dmpInverse a d m - dualDmpInverse a d m
  have ho : oddPart (projection a d) x = x := difference_is_odd hd
  have he : evenPart (projection a d) x = 0 := by
    calc
      _ = evenPart (projection a d) (oddPart (projection a d) x) := by rw [ho]
      _ = 0 := (projection_laws (projection_is_idempotent hd) x).2.1
  change evenPart (projection a d) (x ^ 2) = x ^ 2
  rw [pow_two, (multiplication_rules (projection_is_idempotent hd) x x).1,
    he, ho, zero_mul, zero_add]

section Star
variable [StarRing R]

/-- Taking adjoints exchanges the two orders, without any commuting assumption. -/
theorem star_dmpInverse (a d m : R) :
    star (dmpInverse a d m) = dualDmpInverse (star a) (star d) (star m) := by
  simp only [dmpInverse, dualDmpInverse, star_mul, mul_assoc]

/-- Metric adjoints preserve the even grading for a self-adjoint support. -/
theorem star_evenPart {p : R} (hp : star p = p) (x : R) :
    star (evenPart p x) = evenPart p (star x) := by
  simp only [evenPart, component11, component00, complementIdempotent,
    star_add, star_mul, star_sub, star_one, hp, mul_assoc]

/-- The two off-diagonal corners exchange under adjoints. -/
theorem star_oddPart {p : R} (hp : star p = p) (x : R) :
    star (oddPart p x) = oddPart p (star x) := by
  simp only [oddPart, component10, component01, complementIdempotent,
    star_add, star_mul, star_sub, star_one, hp]
  noncomm_ring

/-- Right multiplication recovers the oblique spectral idempotent. -/
theorem dmp_mul_original (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dmpInverse a d m * a = projection a d := by
  calc
    _ = d * (a * m * a) := by simp only [dmpInverse, mul_assoc]
    _ = d * a := by rw [hm.aba_eq_a]
    _ = projection a d := hd.comm.symm

/-- The opposite ordering recovers the same support on the opposite side. -/
theorem original_mul_dualDmp (hm : IsMoorePenroseInverse a m) :
    a * dualDmpInverse a d m = projection a d := by
  calc
    _ = (a * m * a) * d := by simp only [dualDmpInverse, mul_assoc]
    _ = projection a d := by rw [hm.aba_eq_a]; rfl

omit [StarRing R] in
/-- The outer multiplication is an ordered spectral/metric support product. -/
theorem original_mul_dmp (a d m : R) :
    a * dmpInverse a d m = projection a d * (a * m) := by
  simp only [dmpInverse, projection, mul_assoc]

omit [StarRing R] in
theorem dualDmp_mul_original (hd : IsDrazinInverse a d k) :
    dualDmpInverse a d m * a = (m * a) * projection a d := by
  calc
    _ = (m * a) * (d * a) := by simp only [dualDmpInverse, mul_assoc]
    _ = (m * a) * projection a d := by rw [← hd.comm]; rfl

/-- The target metric support absorbs spectral support from one specified side. -/
theorem target_absorbs_spectral (hm : IsMoorePenroseInverse a m) :
    (a * m) * projection a d = projection a d := by
  change (a * m) * (a * d) = a * d
  rw [← mul_assoc, hm.aba_eq_a]

/-- The source metric support absorbs from the other side. -/
theorem spectral_absorbs_source (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    projection a d * (m * a) = projection a d := by
  change (a * d) * (m * a) = a * d
  rw [hd.comm]
  calc
    (d * a) * (m * a) = d * (a * m * a) := by simp only [mul_assoc]
    _ = d * a := by rw [hm.aba_eq_a]

/-- Sandwiching by the ordered inverses extracts the actual spectral corner of `m`. -/
theorem dmp_sandwich (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    dmpInverse a d m * a * dualDmpInverse a d m =
      projection a d * m * projection a d := by
  rw [dmp_mul_original hd hm, dualDmp_eq_mul_projection, ← mul_assoc]

/-- This is a corner identity, not a claim that the full inverse is even. -/
theorem even_inverse_reconstruction (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    evenPart (projection a d) m =
      dmpInverse a d m * a * dualDmpInverse a d m +
        (1 - projection a d) * m * (1 - projection a d) := by
  rw [dmp_sandwich hd hm]
  rfl

/-- Both hybrid support products are idempotent, not necessarily self-adjoint. -/
theorem hybrid_supports_idempotent (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    IsIdempotentElem (a * dmpInverse a d m) ∧
      IsIdempotentElem (dualDmpInverse a d m * a) := by
  constructor
  · change (a * dmpInverse a d m) * (a * dmpInverse a d m) = _
    calc
      _ = a * (dmpInverse a d m * a * dmpInverse a d m) := by
        simp only [mul_assoc]
      _ = _ := by rw [dmp_outer_inverse hd hm]
  · change (dualDmpInverse a d m * a) * (dualDmpInverse a d m * a) = _
    calc
      _ = (dualDmpInverse a d m * a * dualDmpInverse a d m) * a := by
        simp only [mul_assoc]
      _ = _ := by rw [dualDmp_outer_inverse hd hm]

/-- The inner-inverse defect is exactly the Fitting complementary summand. -/
theorem dmp_inner_defect (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    a - a * dmpInverse a d m * a = fittingNilpotentPart a d := by
  rw [mul_assoc a, dmp_mul_original hd hm]
  simp only [fittingNilpotentPart, complementaryProjection, mul_sub, mul_one]

theorem dualDmp_inner_defect (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    a - a * dualDmpInverse a d m * a = fittingNilpotentPart a d := by
  rw [original_mul_dualDmp hm, projection_comm_self hd]
  simp only [fittingNilpotentPart, complementaryProjection, mul_sub, mul_one]

/-- Being an outer inverse must not be mislabeled as two-sided reflexivity. -/
theorem dmp_inner_iff_nilpotent_part_zero (hd : IsDrazinInverse a d k)
    (hm : IsMoorePenroseInverse a m) :
    a * dmpInverse a d m * a = a ↔ fittingNilpotentPart a d = 0 := by
  rw [← dmp_inner_defect hd hm, sub_eq_zero, eq_comm]

/-- The Penrose arrow respects its distinct source and target reflections. -/
theorem penrose_reflection_intertwining (hm : IsMoorePenroseInverse a m) :
    reflection (a * m) * a = a ∧ a * reflection (m * a) = a := by
  constructor <;>
    simp only [reflection, two_nsmul, mul_sub, sub_mul, mul_add, add_mul,
      mul_one, one_mul, ← mul_assoc, hm.aba_eq_a] <;> abel

/-- The two metric reflections are self-adjoint involutions; they need not coincide. -/
theorem penrose_reflections_unitary (hm : IsMoorePenroseInverse a m) :
    star (reflection (a * m)) * reflection (a * m) = 1 ∧
      star (reflection (m * a)) * reflection (m * a) = 1 := by
  have he : (a * m) * (a * m) = a * m := by
    rw [← mul_assoc, hm.aba_eq_a]
  have hf : (m * a) * (m * a) = m * a := by
    rw [← mul_assoc, hm.bab_eq_b]
  constructor
  · rw [reflection_star hm.ab_adj_eq, reflection_sq he]
  · rw [reflection_star hm.ba_adj_eq, reflection_sq hf]

end Star
end InfoGeometry.Canonical.GradedDMPResolution
