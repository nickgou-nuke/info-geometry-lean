import InfoGeometry.Canonical.ProjectiveStateCore
import InfoGeometry.MeasureProjective.Invariant

/-!
# InfoGeometry.Canonical.RelativeGeneratorCore

Wide relative-generator layer over the nonnegative projective substrate.

This layer stays in the `MeasureProjective` language:
- projective states may have zeros,
- logarithmic generators are carried as wide projective objects,
- gauge laws are phrased almost everywhere / under absolute-continuity hypotheses.

The strict-positive pointwise specialization lives separately in
`RelativePotentialCore` and is connected back through
`PositiveRayProjectiveBridge`.
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
