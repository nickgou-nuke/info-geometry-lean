/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.ZornAssociativeCarrierObstruction

/-!
# Source audit: Zorn carrier cannot inject multiplicatively into an associative semigroup

The obstruction is carrier-specific: an explicit circular associator witness
in `ZornMatrix ℝ`, together with injectivity and multiplicativity, would
transfer associativity back to that carrier. This audit records the axiom
surface of the resulting impossibility theorem.
-/

#print axioms InfoGeometry.Canonical.ZornAssociativeCarrierObstruction.no_injective_mul_map_zorn_to_associative_semigroup
