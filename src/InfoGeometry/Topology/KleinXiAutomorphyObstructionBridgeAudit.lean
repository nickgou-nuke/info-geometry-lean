/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge

/-!
# Source audit: scalar descent through an affine glide

The affine glide squares to vertical translation by twice its parameter.
Therefore any scalar function invariant under the glide must have that
vertical period. This is a conditional obstruction to scalar descent, not a
claim that a particular analytic function has or lacks the period.
-/

#print axioms InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge.affineGlide_square
#print axioms InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge.scalarGlideInvariant_implies_vertical_periodicity
#print axioms InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge.scalarGlideInvariant_implies_vertical_periodicity_on_core
#print axioms InfoGeometry.Topology.KleinXiAutomorphyObstructionBridge.verticalCoordinate_not_scalarGlideInvariant
