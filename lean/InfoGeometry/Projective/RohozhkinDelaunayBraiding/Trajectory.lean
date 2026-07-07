import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.RohozhkinRepresentation
import InfoGeometry.Projective.RohozhkinDelaunayBraiding.AppendixPentagonWord

/-!
# MZM Scrambling Trajectory

A minimal trajectory abstraction for the braid-surface readout.
No further structure is asserted yet; this is a pure data/export boundary.
-/

namespace InfoGeometry.Topology.RohozhkinDelaunayBraiding

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Topology.RohozhkinRepresentation

def MZMScramblingTrajectory (moving : ℕ) : Type _ := DelaunayFlipWord moving

def trajectoryMatrix {moving : ℕ} (T : MZMScramblingTrajectory moving) :
    Matrix (Fin (rohozhkinDim moving)) (Fin (rohozhkinDim moving)) ℚ :=
  rohozhkinMatrix T

/-- Local statement of the five-flip closure for the n = 1 trajectory packet. -/
theorem one_cycle_scramble_identity
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    trajectoryMatrix (moving := 1)
      (appendixPentagonWord zi zj zk zl zm
        (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
          pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
          pentagonGamma1 zi zj zk zl zm =
            (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ))) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) := by
  simpa using appendixPentagonWord_matrix_eq_one zi zj zk zl zm h_il h_ik h_km h_jm h_jl

end InfoGeometry.Topology.RohozhkinDelaunayBraiding
