/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spacetime.BitwistorForwardBackwardSpheres

/-!
# Concrete Integer Example for Section 114: Scalar Quadratic Form
Target: `InfoGeometry/Spacetime/BitwistorForwardBackwardSpheresAudit.lean`

Verifies over `ℤ` (`decide`) that `(13, 3, 4, 12)` and `(13, -3, -4, -12)`
are null for the defined scalar quadratic form, their spatial coordinates sum to
zero, and the sum has quadratic value `676`. This is a coordinate example, not
a physical mass or bitwistor construction.
-/

namespace InfoGeometry.Spacetime.BitwistorAudit

open InfoGeometry.Spacetime.Bitwistor

/-- Concrete integer evaluation of the null-pair quadratic identity. -/
theorem sample_null_pair_quadratic_int :
    let v_fwd : Space3D ℤ := ⟨3, 4, 12⟩
    let v_bwd : Space3D ℤ := ⟨-3, -4, -12⟩
    minkowskiQuadraticCoord 13 v_fwd = 0 ∧
    minkowskiQuadraticCoord 13 v_bwd = 0 ∧
    sumSpaceCoord v_fwd v_bwd = ⟨0, 0, 0⟩ ∧
    minkowskiQuadraticCoord (sumTimeCoord 13 13) (sumSpaceCoord v_fwd v_bwd) = 676 ∧
    2 * (13 * 13 - Space3D.dot v_fwd v_bwd) = 676 := by
  decide

#print axioms InfoGeometry.Spacetime.Bitwistor.quadratic_sum_polarization
#print axioms InfoGeometry.Spacetime.Bitwistor.null_pair_cross_term_identity
#print axioms InfoGeometry.Spacetime.Bitwistor.opposite_spatial_sum_quadratic
#print axioms sample_null_pair_quadratic_int

end InfoGeometry.Spacetime.BitwistorAudit
