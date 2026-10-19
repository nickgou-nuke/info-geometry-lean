/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperGrassmannianMoebiusQuotient

/-!
# Audit: Finite Möbius/Polarization Matrix Identities

This audit reports axiom dependencies for the concrete matrix identities, the
integer sign-parity identity, and the conditional ring-algebra variation lemma.
It does not certify a super-Grassmannian quotient or Berezinian geometry.
-/

namespace InfoGeometry.SuperGrassmannian.MoebiusQuotientAudit

open InfoGeometry.SuperGrassmannian.MoebiusQuotient

#print axioms K_sq_id
#print axioms M_sq_id
#print axioms moebius_anticommutes_polarization
#print axioms moebius_maps_positive_eigenspace_to_negative
#print axioms moebius_metric_isometry
#print axioms moebius_symplectic_anti_invariance
#print axioms nat_sq_parity_iff
#print axioms neg_one_pow_square_eq_self
#print axioms inverse_product_variation_algebraic_identity

end InfoGeometry.SuperGrassmannian.MoebiusQuotientAudit
