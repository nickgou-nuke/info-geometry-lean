import InfoGeometry.MeasureProjective
import InfoGeometry.Measure.Normalized

/-!
# InfoGeometry.Canonical.ProjectiveStateCore

Widened projective root language for nonnegative finite states:
- nonzero unnormalized finite measures
- projective quotient modulo normalization
- canonical normalized slice
- descended logarithmic generator and gauge class

This layer is broader than `PositiveRayCore`: zeros are allowed. Full-support
positive rays are a stricter representation layer sitting above this generalized
projective substrate.
-/

namespace ProjectiveStateCore

export MeasureProjective (
  UState
  NonzeroUState
  SameRay
  sameRaySetoid
  ProjectiveState
  logPotential
  AEAddConst
  PotentialClass
  logPotentialClass
  self_eq_mass_smul_normalize
)

export MeasureProjective.ProjectiveState (
  normalize
  logGenerator
  logGeneratorClass
)

export InfoGeometry.MeasureProjective.Normalized (
  normalizedSlice
  probMeasureToUState
  probMeasureToNonzero
  probMeasureToProjectiveState
  normalize_probMeasureToProjectiveState
  pmfToProbMeasure
  pmfToProjectiveState
  normalize_pmfToProjectiveState
  probMeasureToPMF
  probMeasureToPMF_apply
  probMeasureToPMF_pmfToProbMeasure
  pmfToProbMeasure_probMeasureToPMF
  logPotential_pmf_eq_log_rnDeriv
  logPotential_pmf_self_ae
)

end ProjectiveStateCore
