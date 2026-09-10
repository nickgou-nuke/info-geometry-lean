/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateEvaluation

/-!
# Continuous multiplicativity constraints for Zorn candidates

For fixed canonical Zorn elements, the failure of multiplicativity is a
continuous map into the canonical carrier.  Its zero locus is therefore
closed.  The existing automorphism subgroup is not redefined here.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

noncomputable section

theorem continuous_candidate_multiplicativity_constraint
    (X Y : CZ) :
    Continuous (fun f : SplitAutCandidate =>
      f (zMul X Y) - zMul (f X) (f Y)) := by
  have hxy : Continuous (fun f : SplitAutCandidate => (f X, f Y)) :=
    Continuous.prodMk (continuous_candidate_apply X)
      (continuous_candidate_apply Y)
  have hz : Continuous (fun f : SplitAutCandidate => zMul (f X) (f Y)) :=
    continuous_zMul.comp hxy
  exact continuous_canonicalZorn_sub.comp
    (Continuous.prodMk (continuous_candidate_apply (zMul X Y)) hz)

theorem isClosed_candidate_multiplicativity_constraint
    (X Y : CZ) :
    IsClosed {f : SplitAutCandidate |
      f (zMul X Y) - zMul (f X) (f Y) = 0} := by
  exact isClosed_canonicalZorn_zero.preimage
    (continuous_candidate_multiplicativity_constraint X Y)

theorem continuous_candidate_unit_constraint :
    Continuous (fun f : SplitAutCandidate => f (1 : CZ) - (1 : CZ)) := by
  exact continuous_canonicalZorn_sub.comp
    (Continuous.prodMk (continuous_candidate_apply (1 : CZ)) continuous_const)

theorem isClosed_candidate_unit_constraint :
    IsClosed {f : SplitAutCandidate | f (1 : CZ) - (1 : CZ) = 0} := by
  exact isClosed_canonicalZorn_zero.preimage
    continuous_candidate_unit_constraint

end
end InfoGeometry.Canonical
