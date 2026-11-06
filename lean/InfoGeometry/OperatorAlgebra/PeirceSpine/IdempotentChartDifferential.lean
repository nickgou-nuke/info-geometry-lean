/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartResolvent
import InfoGeometry.OperatorAlgebra.ResolventChartDifferential

/-!
# Resolvent chart derivatives along Peirce directions

The native derivative of the rational coordinate is evaluated at a Peirce
corner and along a direction in that same corner. Orthogonality then turns
the two corner resolvents into the full resolvent of `1 - genV` on both
sides. The tangent direction need not commute with the base point or either
resolvent. These operator-valued derivative identities do not construct a
scalar Hessian, a metric, or a supermanifold.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.OperatorAlgebra.ResolventChartDifferential

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [HasSummableGeomSeries B]

/-- The actual derivative on an arbitrary upper-corner direction is the
full two-sided resolvent sandwich, under one full-denominator unit law. -/
theorem fderiv_resolventChart_conePlus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    fderiv 𝕜 (resolventChart (coneMinus P C)) (conePlus P A) (conePlus P X) =
      Ring.inverse (1 - genV P A C) * conePlus P X *
        Ring.inverse (1 - genV P A C) := by
  rcases (isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit with ⟨hplus, hminus⟩
  rw [fderiv_resolventChart_apply (𝕜 := 𝕜) (coneMinus P C) (conePlus P A)
    (conePlus P X) hplus hminus]
  exact (ringInverse_genV_sandwich_conePlus hP A C X hunit).symm

/-- Reversing the two corners reverses the corner denominators while giving
the same full-resolvent form on a lower-corner direction. -/
theorem fderiv_resolventChart_coneMinus {P : B} (hP : P * P = P) (A C X : B)
    (hunit : IsUnit (1 - genV P A C)) :
    fderiv 𝕜 (resolventChart (conePlus P A)) (coneMinus P C) (coneMinus P X) =
      Ring.inverse (1 - genV P A C) * coneMinus P X *
        Ring.inverse (1 - genV P A C) := by
  rcases (isUnit_one_sub_genV_iff_corner_units hP A C).mp hunit with ⟨hplus, hminus⟩
  rw [fderiv_resolventChart_apply (𝕜 := 𝕜) (conePlus P A) (coneMinus P C)
    (coneMinus P X) hminus hplus]
  exact (ringInverse_genV_sandwich_coneMinus hP A C X hunit).symm

end InfoGeometry.OperatorAlgebra.PeirceSpine
