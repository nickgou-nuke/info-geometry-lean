/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Physics.SpinAffineCasimirRigidity

/-!
# Source audit: ladder-bracket preservation does not preserve the fixed Cartan law

The exact hyperbolic pair preserves the ladder-ladder bracket but violates
the Cartan-ladder relation. Within the stated ansatz, both relations force
`v = 0` and `normSq u = 1`. The separate trace argument rules out nonzero
scalar shifts as similarities.
-/

#print axioms InfoGeometry.Physics.SpinAffineCasimirRigidity.mixed_ladder_bracket
#print axioms InfoGeometry.Physics.SpinAffineCasimirRigidity.mixed_cartan_iff
#print axioms InfoGeometry.Physics.SpinAffineCasimirRigidity.fixed_cartan_spin_relations_iff
#print axioms InfoGeometry.Physics.SpinAffineCasimirRigidity.hyperbolic_counterexample
#print axioms InfoGeometry.Physics.SpinAffineCasimirRigidity.no_similarity_scalar_shift
