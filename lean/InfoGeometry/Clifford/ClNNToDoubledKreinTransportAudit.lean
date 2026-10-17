/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNToDoubledKreinTransport

/-!
# Axiom audit for `ClNNToDoubledKreinTransport`

Direct `#print axioms` checks for the finite-rank coordinate/Euclidean duality
transport and its algebraic-form-to-doubled-Krein identities.
-/

namespace InfoGeometry.Clifford.ClNNToDoubledKreinTransport.Audit

open InfoGeometry.Clifford.ClNNToDoubledKreinTransport

#print axioms rieszEquiv_apply_apply
#print axioms coordinateDualToEuclidean
#print axioms coordinateDual_eval_eq_inner
#print axioms Qsplit_eq_doubledKrein_form
#print axioms evaluation_eq_doubledKrein_cross

end InfoGeometry.Clifford.ClNNToDoubledKreinTransport.Audit
