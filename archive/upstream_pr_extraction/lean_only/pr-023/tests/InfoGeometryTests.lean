import InfoGeometry
import InfoGeometry.Canonical.CasiniBekensteinBound
import InfoGeometry.Canonical.OperatorialFierzDerivationBridge
import InfoGeometry.Canonical.MeasureScaleShape
import InfoGeometry.Canonical.ProjectiveCCR

-- Simple sanity check that key theorems and definitions compile

-- Bekenstein renames
#check InfoGeometry.Canonical.BekensteinBound.TrajectoryRNBarrierNonnegative
#check InfoGeometry.Canonical.BekensteinBound.trajectoryRNBarrierNonnegative_of_sinkhornTrajectory
#check InfoGeometry.Canonical.BekensteinBound.TopologicalBekensteinBound -- deprecated

-- Casini-Bekenstein Bound (True Bound)
#check InfoGeometry.Canonical.CasiniBekenstein.true_bekenstein_bound

-- Operatorial Fierz Derivation (Commutator properties)
#check InfoGeometry.Canonical.OperatorialFierz.innerDerivation
#check InfoGeometry.Canonical.OperatorialFierz.emergentSpacetime_is_derivation

-- Projective CCR (Checking existence of key theorems)
open InfoGeometry.Canonical.ProjectiveCCR
#check ProjectiveBoundaryPacket.vacuumMode_eq_one
#check ProjectiveBoundaryPacket.superKMS_detailed_balance
