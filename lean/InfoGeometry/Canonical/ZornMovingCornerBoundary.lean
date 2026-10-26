/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# Vanishing of the existing operator-valued Zorn moving corner

The owner uses minus-dot diagonal multiplication and a skew cross product.
Parentheses are retained: the full Zorn multiplication is not associative.
No coframe, exterior derivative, or Cartan torsion is defined here.
-/

namespace InfoGeometry.Canonical.ZornMovingCornerBoundary

open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- The exact ordered equation for vanishing of the upper moving corner. -/
theorem moving_corner_eq_zero_iff (X : OpZornMatrix A) (q : OpVec3 A) :
    ((opUnipotentUpper (-q) * X) * opUnipotentUpper q).v = 0 ↔
      OpVec3.leftScale (X.a + OpVec3.dot q X.w) q + X.v =
        OpVec3.rightScale q X.b := by
  rw [(zornRiccati_moving_frame_and_trifactor_fixed_point X 0 0 q 0 0 0).1]
  constructor
  · intro h
    ext
    · have hx := congrArg OpVec3.x h
      simp only [OpVec3.sub_x, OpVec3.add_x, OpVec3.zero_x] at hx ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hx
    · have hy := congrArg OpVec3.y h
      simp only [OpVec3.sub_y, OpVec3.add_y, OpVec3.zero_y] at hy ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hy
    · have hz := congrArg OpVec3.z h
      simp only [OpVec3.sub_z, OpVec3.add_z, OpVec3.zero_z] at hz ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hz
  · intro h
    ext
    · have hx := congrArg OpVec3.x h
      simp only [OpVec3.sub_x, OpVec3.add_x, OpVec3.zero_x] at hx ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hx
    · have hy := congrArg OpVec3.y h
      simp only [OpVec3.sub_y, OpVec3.add_y, OpVec3.zero_y] at hy ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hy
    · have hz := congrArg OpVec3.z h
      simp only [OpVec3.sub_z, OpVec3.add_z, OpVec3.zero_z] at hz ⊢
      simpa only [sub_add_eq_add_sub, sub_eq_zero] using hz

/-- A concrete counterexample prevents the moving corner from being
identified with minus the owner's Riccati expression. -/
theorem moving_corner_not_neg_riccati :
    let X : OpZornMatrix ℚ := opGradeZero 1 0
    let q : OpVec3 ℚ := ⟨1, 0, 0⟩
    ((opUnipotentUpper (-q) * X) * opUnipotentUpper q).v ≠
      -opZornRiccati X q := by
  intro X q h
  have hx := congrArg OpVec3.x h
  norm_num [X, q, opGradeZero, opCartanDiag, opUnipotentUpper,
    opZornRiccati, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] at hx

end InfoGeometry.Canonical.ZornMovingCornerBoundary
