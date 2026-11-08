/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.WuYangNonAbelianDualABInterferometry

/-!
# Audit: Finite Dual-Transformation and Quaternion Interference Identities

The examples instantiate the displayed cross-product transformation and the
native Mathlib quaternion norm/interference statements over `ℤ`. These checks do
not identify the expressions with physical phases, `SU(2)` holonomies, or
normalized transition probabilities.
-/

namespace InfoGeometry.QuantumContext.WuYangDualABAudit

open InfoGeometry.QuantumContext.WuYangDualAB

/-- A finite-coordinate instance of the specified cross-product identity over `ℤ`. -/
theorem sample_dual_cross_product_invariant_int :
    let D : DipoleDoublet ℤ := ⟨⟨1, 2, 3⟩, ⟨4, 5, 6⟩⟩
    let F : EMFieldDoublet ℤ := ⟨⟨7, 8, 9⟩, ⟨2, 1, 4⟩⟩
    dualCrossProductDifference D F = ⟨-8, 4, 0⟩ ∧
    dualCrossProductDifference (maxwellDipoleDual D) (maxwellFieldDual F) =
      ⟨-8, 4, 0⟩ := by
  decide

/-- Ground calculation with Mathlib's quaternion carrier: both input norms are
`30`, their product norm is `900`, and equal amplitudes cancel at scalar `-1`.
This is an unnormalized finite algebraic example. -/
theorem sample_quaternion_interference_int :
    let U : Quaternion ℤ := ⟨1, 2, 3, 4⟩
    let Ψ : Quaternion ℤ := ⟨2, 1, 4, 3⟩
    Quaternion.normSq U = 30 ∧
    Quaternion.normSq Ψ = 30 ∧
    Quaternion.normSq (U * Ψ) = 900 ∧
    quaternionInterferenceNormSq Ψ Ψ (-1) = 0 := by
  norm_num [Quaternion.normSq_def', quaternionInterferenceNormSq]

#print axioms dualCrossProductDifference_maxwell_invariant
#print axioms unit_quaternion_left_mul_preserves_normSq
#print axioms quaternion_interference_normSq_expansion
#print axioms quaternion_interference_normSq_nonneg
#print axioms scalar_minus_one_interference_cancellation
#print axioms sample_dual_cross_product_invariant_int
#print axioms sample_quaternion_interference_int

end InfoGeometry.QuantumContext.WuYangDualABAudit
