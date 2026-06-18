import InfoGeometry.Projective.Bridge
import InfoGeometry.Projective.ConeKL
import InfoGeometry.Projective.CrossRatio
import InfoGeometry.Projective.MobiusGauge
import InfoGeometry.Projective.Dynamics
import InfoGeometry.Projective.FaithfulKL
import InfoGeometry.Projective.GaugeQuotient
import InfoGeometry.Projective.GaugeReduction
import InfoGeometry.Projective.LogSum
import InfoGeometry.Projective.LogSumIneq
import InfoGeometry.Projective.KleinCrossRatioInvariant
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Projective.Quadrics.Polarization
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Projective.KleinQuadricTime
import InfoGeometry.Projective.PenroseSpinTilingConfig
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Projective.KleinQuadricIncidence
import InfoGeometry.Projective.NoncommutativeCrossRatio
import InfoGeometry.Projective.Normalize
import InfoGeometry.Projective.Null
import InfoGeometry.Projective.NullBoundary
import InfoGeometry.Projective.SplitCl44NullBoundary
import InfoGeometry.Projective.Orthant
import InfoGeometry.Projective.PhysicalKinematics
import InfoGeometry.Projective.Projective
import InfoGeometry.Projective.ProjectiveMap
import InfoGeometry.Projective.Quadrics.MonomialBulk2x2
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Projective.Quadrics.Polarization
import InfoGeometry.Projective.Rays
import InfoGeometry.Projective.SelfDualCone
import InfoGeometry.Projective.SplitOctonions
import InfoGeometry.Projective.SplitOctonions.BektasMatrix
import InfoGeometry.Projective.SplitOctonions.BoundaryPacket
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsBarrier
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar
import InfoGeometry.Projective.SplitOctonions.ZornLogVolume
import InfoGeometry.Projective.SplitOctonions.Polar
import InfoGeometry.Projective.SplitOctonions.PolarConcrete
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer
import InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiber
import InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiberTransport
import InfoGeometry.Projective.SplitOctonions.ProjectivePolarInvariant
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsTraceIncidence
import InfoGeometry.Projective.SplitOctonions.ZornInstance
import InfoGeometry.Projective.Twistor.Basic
import InfoGeometry.Projective.Twistor.SplitCl44NullBridge

namespace InfoGeometry

/-!
# InfoGeometry.Projective.All

Stable umbrella module for the projective and self-dual cone layer.
The zero-null twistor bridge remains quarantined and must be imported explicitly.

Split-octonion note:
- `SplitOctonions.Polar` owns projective polar/incidence descent.
- `SplitOctonions.SplitOctonionsBarrier` owns the logarithmic barrier/Hessian
  information-metric slice model.
These are companion lanes (boundary potential vs incidence geometry), not
mutual owner replacements.
-/

end InfoGeometry
