/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ButterflyPaths
import InfoGeometry.Algebra.SpectralFilter
import InfoGeometry.Krein.StructuredTransposeLift
import InfoGeometry.Krein.CayleyGrowthObstruction

/-!
# Regression boundary for the structured-operator synthesis

This entry point exposes the general owners and their concrete obstructions.
It also rejects the inference that merely iterating the idempotency defect
must resolve it. The real fixed point two is an explicit counterexample to
that universal assertion, not a replacement for the matrix recursion.
-/

namespace InfoGeometry.Krein.StructuredOperatorAudit

open InfoGeometry.Core.IdempotencyDefect
open InfoGeometry.Algebra.MatrixDisplacement

/-- Even commuting Boolean addresses can produce noncommuting weighted operators. -/
theorem weighted_shifts_can_fail_to_commute :
    ¬ Commute
      (weightedShift (0 : ZMod 2) (fun j => if j = 0 then (1 : ℚ) else 0))
      (weightedShift 1 (fun _ => (1 : ℚ))) := by
  intro h
  have h0 := (weightedShift_commute_iff _ _ _ _).1 h 0
  norm_num at h0

/-- A nonzero fixed defect, with every finite iterate computed exactly. -/
theorem defect_iterate_two (k : ℕ) : defect^[k] (2 : ℝ) = 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      norm_num [defect]

/-- Recursion alone does not force a final zero defect. -/
theorem defect_tower_need_not_resolve :
    ¬ ∀ x : ℝ, ∃ k : ℕ, defect^[k] x = 0 := by
  intro h
  obtain ⟨k, hk⟩ := h 2
  rw [defect_iterate_two] at hk
  norm_num at hk

end InfoGeometry.Krein.StructuredOperatorAudit

#print axioms InfoGeometry.Algebra.MatrixDisplacement.weightedShift_mul
#print axioms InfoGeometry.Algebra.MatrixDisplacement.coefficient_mul
#print axioms InfoGeometry.Algebra.MatrixDisplacement.prod_weightedShift
#print axioms InfoGeometry.Algebra.ButterflyPaths.prod_bitStep_eq_sum_weightedShift
#print axioms InfoGeometry.Algebra.MatrixDisplacement.iterate_bitStep
#print axioms InfoGeometry.Algebra.MatrixDisplacement.iterate_mem_displacementSubring
#print axioms InfoGeometry.Algebra.MonarchFactorization.routingSlice_monarch_rank_le_one
#print axioms InfoGeometry.Algebra.MonarchFactorization.FourStateWitness.witness_square_not_isMonarch
#print axioms InfoGeometry.Algebra.SpectralFilter.filter_list_prod
#print axioms InfoGeometry.Algebra.SpectralFilter.filter_idempotent_iff
#print axioms InfoGeometry.Algebra.CayleyForm.cayley_preserves_form
#print axioms InfoGeometry.Krein.StructuredTransposeLift.frame_weighted_product_defect
#print axioms InfoGeometry.Krein.StructuredTransposeLift.lift_monarch_mul_eq_iff
#print axioms InfoGeometry.Krein.CayleyGrowthObstruction.boost_pow_preserves_grading
#print axioms InfoGeometry.Krein.CayleyGrowthObstruction.boost_energy_unbounded
#print axioms InfoGeometry.Krein.CayleyGrowthObstruction.one_add_swap_has_no_right_inverse
#print axioms InfoGeometry.Krein.StructuredOperatorAudit.weighted_shifts_can_fail_to_commute
#print axioms InfoGeometry.Krein.StructuredOperatorAudit.defect_tower_need_not_resolve
