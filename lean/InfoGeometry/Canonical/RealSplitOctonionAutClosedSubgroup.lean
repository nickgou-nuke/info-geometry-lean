/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutClosedLocus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Native closed-subgroup packaging

The existing algebraic automorphism subgroup is packaged as Mathlib's native
`ClosedSubgroup`.  This is the endpoint needed before any separate manifold
construction; it does not assert that Mathlib can automatically infer one.
-/

namespace InfoGeometry.Canonical

noncomputable section

def closedSplitOctonionAutSubgroup :
    ClosedSubgroup (SplitOctonionAutCandidate ℝ) where
  toSubgroup := splitOctonionAutSubgroup (R := ℝ)
  isClosed' := by
    simpa only [SplitOctonionAutSet] using
      isClosed_splitOctonionAutSet

@[simp] theorem closedSplitOctonionAutSubgroup_coe :
    (closedSplitOctonionAutSubgroup : Set (SplitOctonionAutCandidate ℝ)) =
      SplitOctonionAutSet (R := ℝ) := by
  rfl

end
end InfoGeometry.Canonical
