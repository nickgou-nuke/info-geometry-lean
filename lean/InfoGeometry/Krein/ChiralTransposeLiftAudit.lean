/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.ChiralTransposeLift

/-!
# Noncommutative regression witnesses for the chiral transpose lift

The general owner is unrestricted in finite dimension. These small witnesses
exercise the two false generalizations rejected by its theorem contract:
unconditional product preservation and a diagonal square in the original frame.
-/

namespace InfoGeometry.Krein.ChiralTransposeLiftAudit

open Matrix InfoGeometry.Krein.ChiralTransposeLift

def forward : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def backward : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem forward_backward_noncommute : ¬ Commute forward backward := by
  intro h
  have h00 := congrFun (congrFun h.eq 0) 0
  norm_num [forward, backward, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem lift_forward_backward_product_ne :
    lift forward * lift backward ≠ lift (forward * backward) := by
  intro h
  exact forward_backward_noncommute ((lift_mul_eq_iff forward backward).1 h)

/-- The retained off-diagonal commutator is already nonzero for a directed edge. -/
theorem contraction_square_offDiagonal_entry :
    (contraction forward * contraction forward) (Sum.inl 0) (Sum.inr 0) =
      (-1 / 2 : ℝ) := by
  rw [contraction_square]
  norm_num [reversiblePart, circulatingPart, forward, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.fromBlocks]

end InfoGeometry.Krein.ChiralTransposeLiftAudit

#print axioms InfoGeometry.Krein.ChiralTransposeLift.frame_product_defect
#print axioms InfoGeometry.Krein.ChiralTransposeLift.lift_mul_eq_iff
#print axioms InfoGeometry.Krein.ChiralTransposeLift.defect_iterate_lift
#print axioms InfoGeometry.Krein.ChiralTransposeLift.frame_defect_iterate_lift
#print axioms InfoGeometry.Krein.ChiralTransposeLift.lift_idempotent_iff
#print axioms InfoGeometry.Krein.ChiralTransposeLift.lift_jordan
#print axioms InfoGeometry.Krein.ChiralTransposeLift.lift_sandwich
#print axioms InfoGeometry.Krein.ChiralTransposeLift.framed_compression_flag_defect
#print axioms InfoGeometry.Krein.ChiralTransposeLift.lift_kreinSelfAdjoint
#print axioms InfoGeometry.Krein.ChiralTransposeLift.frame_contraction_square
#print axioms InfoGeometry.Krein.ChiralTransposeLift.contraction_square
#print axioms InfoGeometry.Krein.ChiralTransposeLift.defect_lift_blocks
#print axioms InfoGeometry.Krein.ChiralTransposeLift.gram_difference
#print axioms InfoGeometry.Krein.ChiralTransposeLift.nullPlus_krein_null
#print axioms InfoGeometry.Krein.ChiralTransposeLift.nullMinus_krein_null
#print axioms InfoGeometry.Krein.ChiralTransposeLift.null_cross_pairing
#print axioms InfoGeometry.Krein.ChiralTransposeLift.swap_antiIsometry
#print axioms InfoGeometry.Krein.ChiralTransposeLift.swap_grading_square
#print axioms InfoGeometry.Krein.ChiralTransposeLiftAudit.lift_forward_backward_product_ne
#print axioms InfoGeometry.Krein.ChiralTransposeLiftAudit.contraction_square_offDiagonal_entry
