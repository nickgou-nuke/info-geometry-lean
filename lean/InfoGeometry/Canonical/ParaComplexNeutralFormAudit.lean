/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParaComplexNeutralForm

/-!
# Axiom Audit: ParaComplexNeutralForm

Auditing all axioms used in ParaComplexNeutralForm.
Expected: standard Lean 4 foundational axioms only (`propext`, `Classical.choice`, `Quot.sound`).
No custom axioms, no sorry, no admit.
-/

#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.plus_projector_isotropic
#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.minus_projector_isotropic
#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.antiCompatible_of_anti_isometry
#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.form_self_eq_cross_pairing_sum
#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.form_self_eq_two_mul_cross_pairing
#print axioms InfoGeometry.Canonical.ParaComplexNeutralForm.eigenspaces_disjoint
