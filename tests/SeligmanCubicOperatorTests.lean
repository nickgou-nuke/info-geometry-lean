/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornCubicOperatorGeometry

/-!
Semantic regressions on the actual split Albert carrier: its nondegenerate
pairing has nonzero isotropic vectors and negative values, and its operator
product has a nonzero off-diagonal commutator. These prevent replacing split
bilinear geometry by a positive-definite or commuting model.
-/

namespace InfoGeometry.Tests.SeligmanCubicOperator

open InfoGeometry.Algebra InfoGeometry.Algebra.H3Zorn

theorem offDiagonal_isotropic_nonzero :
    traceBilin (h3_off₁₂ 1) (h3_off₁₂ 1) = 0 ∧ h3_off₁₂ 1 ≠ 0 := by
  constructor
  · norm_num [traceBilin, h3_off₁₂, zorn_basis, ZornVectorMatrix.trace,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.zero,
      ZornVec3.dot, Fin.sum_univ_three]
  · intro h
    have hv := congrArg (fun x : H3Zorn ℝ => x.a.v 0) h
    change (1 : ℝ) = 0 at hv
    norm_num at hv

theorem offDiagonal_pairing_negative :
    traceBilin (h3_off₁₂ 1 + h3_off₁₂ 4) (h3_off₁₂ 1 + h3_off₁₂ 4) = -2 := by
  norm_num [traceBilin, h3_off₁₂, zorn_basis, add_readback,
    ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVec3.dot, Fin.sum_univ_three]

theorem distinguished_unit_pairing_positive : traceBilin (1 : H3Zorn ℝ) 1 = 3 := by
  rw [traceBilin_one]
  change (1 : ℝ) + 1 + 1 = 3
  norm_num

/-- The commutator is evaluated before any scalar coordinate is read. -/
theorem offDiagonal_compositions_act_differently :
    (jordanLmul (R := ℝ) (h3_off₁₂ 1) * jordanLmul (R := ℝ) (h3_off₂₃ 2))
        (h3_off₂₃ 3) ≠
      (jordanLmul (R := ℝ) (h3_off₂₃ 2) * jordanLmul (R := ℝ) (h3_off₁₂ 1))
        (h3_off₂₃ 3) := by
  intro h
  have hz : jordanInnerDerivation (R := ℝ) (h3_off₁₂ 1) (h3_off₂₃ 2)
      (h3_off₂₃ 3) = 0 := sub_eq_zero.mpr h
  have hc := congrArg (fun x : H3Zorn ℝ => x.a.b) hz
  rw [h3Zorn_offDiagonal_commutator_coordinate] at hc
  change -(1 / 4 : ℝ) = 0 at hc
  norm_num at hc

end InfoGeometry.Tests.SeligmanCubicOperator
