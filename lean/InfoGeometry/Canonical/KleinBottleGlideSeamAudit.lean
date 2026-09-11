/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.KleinBottleGlideSeam

/-!
# Axiom Audit: KleinBottleGlideSeam

Auditing all axioms used in KleinBottleGlideSeam.
Expected: standard Lean 4 foundational axioms only (`propext`, `Classical.choice`, `Quot.sound`).
Zero custom axioms, zero sorry, zero admit.
-/

open InfoGeometry.Canonical.KleinBottleGlideSeam.ParaComplex

#print axioms is_on_real_seam_iff_tau_zero
#print axioms glide_pair_eq
#print axioms glide_preserves_real_seam
#print axioms transverse_fixed_locus
#print axioms glide_on_seam_is_pure_translation
#print axioms glide_iter_two
#print axioms glideZ_iter_two
