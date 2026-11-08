/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FixedPairingTorsionBoundary
open InfoGeometry.Canonical.FixedPairingTorsionBoundary

#print axioms fixed_pair_double_zero
#print axioms fixed_pair_zero
#print axioms coefficientForm_anti
#print axioms two_torsion_free_iff_bilinear_fixed_pairing
#print axioms zmod6_bilinear_boundary

example : coefficientForm (3 : ZMod 6) 1 1 ≠ 0 := zmod6_bilinear_boundary.2.2

example : ∀ a : ℤ, 2*a=0 → a=0 := by
  intro a ha
  omega
