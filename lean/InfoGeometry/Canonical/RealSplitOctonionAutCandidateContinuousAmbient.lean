/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateAmbient

/-!
# Continuous ambient action for all linear Zorn candidates

This owner upgrades the already-proved Cartesian conjugation action to the
native continuous-linear-equivalence carrier.  It does not introduce a
topology or a manifold structure on the candidate carrier.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable section

theorem candidateCartesianContinuousLinearEquiv_one :
    candidateCartesianContinuousLinearEquiv (1 : SplitAutCandidate) =
      ContinuousLinearEquiv.refl ℝ CartesianCoordinates := by
  apply ContinuousLinearEquiv.ext
  funext q
  change candidateCartesianLinearEquiv (1 : SplitAutCandidate) q = q
  rw [candidateCartesianLinearEquiv_one]
  rfl

theorem candidateCartesianContinuousLinearEquiv_mul (f g : SplitAutCandidate) :
    candidateCartesianContinuousLinearEquiv (f * g) =
      candidateCartesianContinuousLinearEquiv f *
        candidateCartesianContinuousLinearEquiv g := by
  apply ContinuousLinearEquiv.ext
  funext q
  change candidateCartesianLinearEquiv (f * g) q =
    (candidateCartesianLinearEquiv f *
      candidateCartesianLinearEquiv g) q
  rw [candidateCartesianLinearEquiv_mul]

noncomputable def candidateCartesianContinuousHom :
    SplitAutCandidate →* (CartesianCoordinates ≃L[ℝ] CartesianCoordinates) where
  toFun := candidateCartesianContinuousLinearEquiv
  map_one' := candidateCartesianContinuousLinearEquiv_one
  map_mul' := candidateCartesianContinuousLinearEquiv_mul

end
end InfoGeometry.Canonical
