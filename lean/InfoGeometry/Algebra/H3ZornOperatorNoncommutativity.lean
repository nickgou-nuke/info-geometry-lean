/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Noncommuting operators from three nonscalar Albert Peirce elements

All three inputs have zero Albert diagonal coordinates. Their octonion blocks
are the distinct upper Zorn generators `U 0`, `U 1`, and `U 2`. The resulting
composition commutator is nonzero on the full split Albert carrier. The
calculation therefore checks order-sensitive exceptional multiplication, not
just a scalar or diagonal subalgebra.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- A coordinate of the full operator commutator detects its nonzero action. -/
theorem h3Zorn_offDiagonal_commutator_coordinate :
    (jordanInnerDerivation (R := ℝ) (h3_off₁₂ 1) (h3_off₂₃ 2) (h3_off₂₃ 3)).a.b =
      -(1 / 4 : ℝ) := by
  change (candidateJordanMul (h3_off₁₂ 1)
      (candidateJordanMul (h3_off₂₃ 2) (h3_off₂₃ 3)) -
    candidateJordanMul (h3_off₂₃ 2)
      (candidateJordanMul (h3_off₁₂ 1) (h3_off₂₃ 3))).a.b = _
  simp only [candidateJordanMul_trace_formula]
  norm_num [h3_off₁₂, h3_off₂₃, zorn_basis, linearTrace, crossProduct, adjointQuad,
    add_readback, sub_readback, neg_readback, smul_readback, H3Zorn.one,
    ZornVectorMatrix.norm, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.add, ZornVectorMatrix.sub,
    ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- The actual Albert multiplication operators have a nonzero commutator. -/
theorem h3Zorn_offDiagonal_innerDerivation_ne_zero :
    jordanInnerDerivation (R := ℝ) (h3_off₁₂ 1) (h3_off₂₃ 2) ≠ 0 := by
  intro h
  have hx := congrArg (fun D : Module.End ℝ (H3Zorn ℝ) => (D (h3_off₂₃ 3)).a.b) h
  rw [h3Zorn_offDiagonal_commutator_coordinate] at hx
  change -(1 / 4 : ℝ) = 0 at hx
  norm_num at hx

/-- The composition product in the full endomorphism algebra is genuinely
noncommutative on these off-diagonal Albert multiplication operators. -/
theorem h3Zorn_offDiagonal_operator_products_ne :
    jordanLmul (R := ℝ) (h3_off₁₂ 1) * jordanLmul (R := ℝ) (h3_off₂₃ 2) ≠
      jordanLmul (R := ℝ) (h3_off₂₃ 2) * jordanLmul (R := ℝ) (h3_off₁₂ 1) := by
  intro h
  apply h3Zorn_offDiagonal_innerDerivation_ne_zero
  change _ - _ = 0
  exact sub_eq_zero.mpr h

/-- A nonzero element of the actual derivation subalgebra, not an assumed
dimension or classification certificate. -/
theorem h3Zorn_offDiagonal_bundledDerivation_ne_zero :
    h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₂₃ 2) ≠ 0 := by
  intro h
  apply h3Zorn_offDiagonal_innerDerivation_ne_zero
  exact congrArg (fun D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ) =>
    (D : Module.End ℝ (H3Zorn ℝ))) h

end InfoGeometry.Algebra
