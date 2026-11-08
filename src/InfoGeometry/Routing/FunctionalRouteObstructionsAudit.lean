/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FunctionalRouteObstructions

/-! Kernel dependencies of the route counterexamples and synchronized
retraction replacement. Existence of a certificate for every route and
commutation of arbitrary support projections are not asserted. -/

open InfoGeometry.Routing.FunctionalRouteObstructions
open InfoGeometry.Routing.FunctionalRouteCore

#print axioms sibling_contrast_dies
#print axioms chain_supports_do_not_commute
#print axioms chain_squared_charge_not_idempotent
#print axioms constant_inverse_not_core_transpose
#print axioms drazin_of_synchronized_retraction
#print axioms synchronized_projection
#print axioms inverse_factorization
#print axioms core_factorization
#print axioms mp_of_split_factorization
