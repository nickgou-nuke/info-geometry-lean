/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateContinuousAmbient
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Induced topology on the full linear candidate carrier

The topology is pulled back from the native continuous-linear-equivalence
ambient group through the already faithful candidate action.  This file does
not assert closedness, a manifold structure, or a Lie-group instance.
-/

namespace InfoGeometry.Canonical

noncomputable section

noncomputable instance instTopologicalSpaceCandidate : TopologicalSpace SplitAutCandidate :=
  TopologicalSpace.induced candidateCartesianContinuousHom inferInstance

noncomputable instance instIsTopologicalGroupCandidate : IsTopologicalGroup SplitAutCandidate :=
  topologicalGroup_induced candidateCartesianContinuousHom

end
end InfoGeometry.Canonical
