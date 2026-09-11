/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ambient action of candidate split-octonion automorphisms

The full linear-equivalence carrier is treated before restricting to the
existing multiplicativity subgroup.  Conjugation is proved algebraically;
the continuous upgrade reuses the same underlying equivalence.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable section

abbrev SplitAutCandidate := SplitOctonionAutCandidate ℝ


def candidateCartesianLinearEquiv (f : SplitAutCandidate) :
    CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates :=
  cartesianZornLinearEquiv.trans (f.trans cartesianZornLinearEquiv.symm)

@[simp] theorem candidateCartesianLinearEquiv_apply
    (f : SplitAutCandidate) (q : CartesianCoordinates) :
    candidateCartesianLinearEquiv f q =
      cartesianZornLinearEquiv.symm
        (f (cartesianZornLinearEquiv q)) :=
  rfl

theorem candidateCartesianLinearEquiv_one :
    candidateCartesianLinearEquiv (1 : SplitAutCandidate) =
      LinearEquiv.refl ℝ CartesianCoordinates := by
  apply LinearEquiv.ext
  intro q
  change cartesianZornLinearEquiv.symm
      (cartesianZornLinearEquiv q) = q
  exact cartesianZornLinearEquiv.symm_apply_apply q

theorem candidateCartesianLinearEquiv_mul (f g : SplitAutCandidate) :
    candidateCartesianLinearEquiv (f * g) =
      candidateCartesianLinearEquiv f * candidateCartesianLinearEquiv g := by
  apply LinearEquiv.ext
  intro q
  change cartesianZornLinearEquiv.symm
      ((f * g) (cartesianZornLinearEquiv q)) =
    cartesianZornLinearEquiv.symm
      (f (cartesianZornLinearEquiv
        (cartesianZornLinearEquiv.symm (g (cartesianZornLinearEquiv q)))))
  simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

noncomputable def candidateCartesianContinuousLinearEquiv (f : SplitAutCandidate) :
    CartesianCoordinates ≃L[ℝ] CartesianCoordinates :=
  (candidateCartesianLinearEquiv f).toContinuousLinearEquiv

@[simp] theorem candidateCartesianContinuousLinearEquiv_apply
    (f : SplitAutCandidate) (q : CartesianCoordinates) :
    candidateCartesianContinuousLinearEquiv f q =
      candidateCartesianLinearEquiv f q :=
  rfl

end
end InfoGeometry.Canonical
