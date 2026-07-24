import InfoGeometry
import InfoGeometry.Canonical.CasiniBekensteinBound
import InfoGeometry.Canonical.OperatorialFierzDerivationBridge
import InfoGeometry.Canonical.MeasureScaleShape
import InfoGeometry.Canonical.ProjectiveCCR
import InfoGeometry.Canonical.ComplexAnalyticBridge

-- Simple sanity check that key theorems and definitions compile

-- Bekenstein current surface
#check InfoGeometry.Canonical.BekensteinBound.trajectoryRNBarrier_nonneg
#check InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_sinkhornTrajectory
#check InfoGeometry.Canonical.BekensteinBound.TopologicalBekensteinBound

-- Casini-Bekenstein Bound (True Bound)
#check InfoGeometry.Canonical.CasiniBekenstein.true_bekenstein_bound

-- Operatorial Fierz Derivation (Commutator properties)
#check InfoGeometry.Canonical.OperatorialFierz.innerDerivation
#check InfoGeometry.Canonical.OperatorialFierz.emergentSpacetime_is_derivation

-- Projective CCR current surface
open InfoGeometry.Canonical.ProjectiveCCR
#check ProjectiveBoundaryPacket
#check ProjectiveBoundaryPacket.mk
#check ProjectiveBoundaryPacket.cones
#check ProjectiveBoundaryPacket.gap
#check ProjectiveBoundaryPacket.zeroMode
#check ProjectiveBoundaryPacket.kms

-- Complex analytic doubled bridge
open InfoGeometry.Canonical.ComplexAnalyticBridge
#check analyticAt_liftedToDoubled_cauchyAnalyticAt
#check complexDoubledCLE
#check lifted
#check clockAxis_complexToDoubled

-- Zero-holonomy / primitive exactness bridge
open InfoGeometry.Canonical.ZeroHolonomyAnalyticity
#check isExactOn_to_analyticAt
#check isExactOn_to_cauchyAnalyticAt
#check isExactOn_to_doubled_cauchyAnalyticAt
#check primitiveExactness_to_zeroHolonomy_cauchyAnalyticAt
#check primitiveExactness_to_zeroHolonomy_doubled_cauchyAnalyticAt

example (z : ℂ) : doubledToComplex (complexToDoubled z) = z := by
  simp

example (v : InfoGeometry.Krein.DoubledSpace ℝ) :
    complexToDoubled (doubledToComplex v) = v := by
  simp
