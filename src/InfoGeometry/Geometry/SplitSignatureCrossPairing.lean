/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Split signature and the real chiral cross-pairing

For two vectors in a real inner-product space, the difference of their squared
norms becomes a cross-pairing after the real 45 degree change of variables
`a = (p + q) / sqrt 2`, `b = (p - q) / sqrt 2`.  This is an elementary
coordinate identity; it does not identify the two summands or introduce a
new Clifford carrier.
-/

namespace InfoGeometry.Geometry.SplitSignatureCrossPairing

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The split quadratic form on a pair of vectors. -/
def splitSignature (p q : E) : ℝ :=
  ⟪p, p⟫_ℝ - ⟪q, q⟫_ℝ

/-- Positive chiral coordinate in the real 45 degree basis. -/
noncomputable def chiralPlus (p q : E) : E :=
  (Real.sqrt 2)⁻¹ • (p + q)

/-- Negative chiral coordinate in the real 45 degree basis. -/
noncomputable def chiralMinus (p q : E) : E :=
  (Real.sqrt 2)⁻¹ • (p - q)

theorem splitSignature_eq_two_inner_chiral (p q : E) :
    splitSignature p q =
      2 * ⟪chiralPlus p q, chiralMinus p q⟫_ℝ := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity
  rw [splitSignature, chiralPlus, chiralMinus]
  rw [real_inner_smul_left, real_inner_smul_right]
  simp only [inner_add_left, inner_sub_right]
  have hqp : ⟪q, p⟫_ℝ = ⟪p, q⟫_ℝ := (real_inner_comm q p).symm
  rw [hqp]
  field_simp [hsqrt_ne]
  rw [hsqrt]
  ring

theorem splitSignature_eq_inner_add_sub (p q : E) :
    splitSignature p q = ⟪p + q, p - q⟫_ℝ := by
  rw [splitSignature]
  simp only [inner_add_left, inner_sub_right]
  have hqp : ⟪q, p⟫_ℝ = ⟪p, q⟫_ℝ := (real_inner_comm q p).symm
  rw [hqp]
  ring

theorem null_iff_chiral_orthogonal (p q : E) :
    splitSignature p q = 0 ↔
      ⟪chiralPlus p q, chiralMinus p q⟫_ℝ = 0 := by
  rw [splitSignature_eq_two_inner_chiral]
  constructor <;> intro h
  · linarith
  · linarith

end InfoGeometry.Geometry.SplitSignatureCrossPairing
