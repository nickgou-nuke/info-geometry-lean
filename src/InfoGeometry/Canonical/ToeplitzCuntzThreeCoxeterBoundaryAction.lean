import InfoGeometry.Topology.ToeplitzCuntzThreeTrialityBoundaryGroupoidColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis

/-!
# The concrete order-three Coxeter action on the ternary boundary

The existing groupoid owner supplies the boundary and coordinatewise color
action.  This file identifies the already formalized cyclic color permutation
with its order-three boundary homeomorphism and proves prefix covariance.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction

open InfoGeometry.Canonical
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

def coxeterBoundaryHomeomorph :
    TernaryBoundary ≃ₜ TernaryBoundary :=
  boundaryPermutationHomeomorph trialityCyclePerm

theorem coxeterBoundaryHomeomorph_cube (x : TernaryBoundary) :
    coxeterBoundaryHomeomorph
        (coxeterBoundaryHomeomorph
          (coxeterBoundaryHomeomorph x)) = x := by
  funext n
  change trialityPermute (trialityPermute (trialityPermute (x n))) = x n
  exact triality_order_three (x n)

@[simp] theorem coxeterBoundary_prefix
    (c : ColorChannel) (x : TernaryBoundary) :
    boundaryPermutation trialityCyclePerm (prefixBoundary c x) =
      prefixBoundary (trialityCyclePerm c)
        (boundaryPermutation trialityCyclePerm x) := by
  exact boundaryPermutation_prefix trialityCyclePerm c x

end InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
