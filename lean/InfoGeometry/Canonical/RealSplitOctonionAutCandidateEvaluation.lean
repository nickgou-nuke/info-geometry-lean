/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Evaluation of the full candidate carrier

Evaluation is continuous for the topology induced by the faithful Cartesian
ambient action.  The result is stated on the canonical Zorn carrier, so it is
ready for the multiplicativity constraint without introducing a second
automorphism type.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable section

theorem continuous_candidate_apply (X : CZ) :
    Continuous (fun f : SplitAutCandidate => f X) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun f : SplitAutCandidate =>
    cartesianZornLinearEquiv.symm (f X))
  have hf : Continuous (fun f : SplitAutCandidate =>
      candidateCartesianContinuousLinearEquiv f) :=
    continuous_induced_dom
  have hu : Continuous (fun f : CartesianCoordinates ≃L[ℝ] CartesianCoordinates =>
      continuousLinearEquivToUnitHom f) :=
    continuous_induced_dom
  have hc : Continuous (fun f : CartesianCoordinates ≃L[ℝ] CartesianCoordinates =>
      (continuousLinearEquivToUnitHom f :
        CartesianCoordinates →L[ℝ] CartesianCoordinates)) :=
    Units.continuous_val.comp hu
  have he : Continuous (fun f : SplitAutCandidate =>
      candidateCartesianContinuousLinearEquiv f
        (cartesianZornLinearEquiv.symm X)) :=
    (ContinuousLinearMap.apply ℝ CartesianCoordinates
      (cartesianZornLinearEquiv.symm X)).continuous.comp (hc.comp hf)
  simpa only [candidateCartesianContinuousLinearEquiv_apply,
    candidateCartesianLinearEquiv_apply,
    LinearEquiv.apply_symm_apply] using he

end
end InfoGeometry.Canonical
