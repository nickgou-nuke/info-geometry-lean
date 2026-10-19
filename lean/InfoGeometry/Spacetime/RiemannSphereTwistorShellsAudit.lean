/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spacetime.RiemannSphereTwistorShells

/-!
# Concrete Integer Examples for Section 113: Light-Shell Polynomial Identities
Target: `InfoGeometry/Spacetime/RiemannSphereTwistorShellsAudit.lean`

Verifies over `ℤ` (`decide`) the scalar light-shell equation and the interior
quadratic value at a concrete Pythagorean quadruple. No twistor or modular-time
construction is asserted.
-/

namespace InfoGeometry.Spacetime.RiemannShellsAudit

open InfoGeometry.Spacetime.RiemannShells

/-- Concrete light-shell point `(13, 3, 4, 12)` and interior polynomial value. -/
theorem sample_pythagorean_light_shell_int :
    let v : Space3D ℤ := ⟨3, 4, 12⟩
    radiusSq v = 169 ∧
    isLightShell 13 v ∧
    hermitianBispinorDet 13 v = 0 ∧
    hermitianBispinorDet 14 v = 27 ∧
    0 < hermitianBispinorDet 14 v := by
  norm_num [isLightShell, radiusSq, hermitianBispinorDet, det2]

#print axioms InfoGeometry.Spacetime.RiemannShells.sampleSpace3DInt_ne_zero
#print axioms InfoGeometry.Spacetime.RiemannShells.bispinor_det_eq_hermitianBispinorDet
#print axioms InfoGeometry.Spacetime.RiemannShells.hermitianBispinorDet_is_minkowski
#print axioms InfoGeometry.Spacetime.RiemannShells.bispinor_det_is_minkowski
#print axioms InfoGeometry.Spacetime.RiemannShells.light_shell_hermitianBispinorDet_zero
#print axioms InfoGeometry.Spacetime.RiemannShells.light_shell_bispinor_det_zero
#print axioms InfoGeometry.Spacetime.RiemannShells.time_cone_det_strictly_positive
#print axioms sample_pythagorean_light_shell_int

end InfoGeometry.Spacetime.RiemannShellsAudit
