import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.RohozhkinRepresentation

/-!
# Rohozhkin Delaunay Braiding

Conservative scaffolding that exposes Rohozhkin Appendix-A pentagon flips as a
concrete five-flip flip-word layer for the braid trajectory model.

This file stays in the finite-rational Delaunay layer. It does **not** assert a
complete physical identification with amplituhedra, anyonic channels, RK invariants,
or a nontrivial global generator assignment.
-/

namespace InfoGeometry.Topology.RohozhkinDelaunayBraiding

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary
open RohozhkinRepresentation

/-- The Appendix A five-flip word in the `n = 1` Delaunay presentation layer. -/
noncomputable def appendixPentagonWord
    (zi zj zk zl zm : ℚ) : DelaunayFlipWord 1 :=
  { flips := appendixPentagonContexts zi zj zk zl zm }

/-- The Appendix A pentagon word evaluates to the identity transport matrix. -/
theorem appendixPentagonWord_matrix_eq_one
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    rohozhkinMatrix
      (appendixPentagonWord zi zj zk zl zm) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) := by
  simpa [appendixPentagonWord] using
    (tiling_pentagon_braid_readout zi zj zk zl zm
      h_il h_ik h_km h_jm h_jl
      ([] : List (DelaunayFlipContext 1)) ([] : List (DelaunayFlipContext 1)))

/-- The Appendix A pentagon word is equivalent to the empty word in the Delaunay
quotient relation. -/
theorem appendixPentagonWord_equiv_empty
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    DelaunayEquiv
      (appendixPentagonWord zi zj zk zl zm)
      ({ flips := [] } :
         DelaunayFlipWord 1) := by
  simpa [appendixPentagonWord] using
    (appendix_pentagon_delaunay_equiv zi zj zk zl zm
      h_il h_ik h_km h_jm h_jl
      ([] : List (DelaunayFlipContext 1)) ([] : List (DelaunayFlipContext 1)))

/--
A minimal trajectory abstraction for the braid-surface readout.
No further structure is asserted yet; this is a pure data/export boundary.
-/
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
      (appendixPentagonWord zi zj zk zl zm) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) := by
  simpa using appendixPentagonWord_matrix_eq_one zi zj zk zl zm h_il h_ik h_km h_jm h_jl

end InfoGeometry.Topology.RohozhkinDelaunayBraiding
