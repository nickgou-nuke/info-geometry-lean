/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceReflectionClaimBoundaries
open InfoGeometry.Canonical.PeirceReflectionClaimBoundaries
#print axioms selfAdjoint_not_square_one
#print axioms six_seed_pair
#print axioms six_noncommuting
#print axioms nonzero_wall_can_be_reflection_invariant
#print axioms defect_zero_iff

example : wall ≠ 0 := nonzero_wall_can_be_reflection_invariant.2.2.1
example : reflection * wall * reflection - wall = 0 := by
  rw [nonzero_wall_can_be_reflection_invariant.2.2.2, sub_self]
