/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ProjectiveStateCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MeasureProjective.Invariant

/-!
# InfoGeometry.Canonical.RelativeGeneratorCore

Wide relative-generator layer over the nonnegative projective substrate.

This layer stays in the `MeasureProjective` language:
- projective states may have zeros,
- logarithmic generators are carried as wide projective objects,
- gauge laws are phrased almost everywhere / under absolute-continuity hypotheses.

The strict-positive pointwise specialization lives in `RelativePotentialCore`
and is connected to the discrete projective model by
`RelativePotentialDiscreteBridge`.
-/

namespace InfoGeometry.Canonical.RelativeGeneratorCore

export InfoGeometry.MeasureProjective (
  logPotential
  AEAddConst
  PotentialClass
  logPotentialClass
  logPotential_smul_left_ae
  logPotential_smul_right_ae
)

export InfoGeometry.MeasureProjective.ProjectiveState (
  logGenerator
  logGeneratorClass
  logGenerator_self
)

export InfoGeometry.MeasureProjective (
  logGeneratorClass_invariant
)

end InfoGeometry.Canonical.RelativeGeneratorCore
