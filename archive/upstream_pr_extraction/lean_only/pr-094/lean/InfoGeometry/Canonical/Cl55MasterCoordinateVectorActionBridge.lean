import InfoGeometry.Canonical.Cl55MasterCoordinateChiralBlockBridge

/-!
# Vector-action transport for the reindexed `Cl(5,5)` master carrier

The matrix reindexing is now accompanied by its native vector action.  This
owner uses Mathlib's `Matrix.mulVecLin_reindex`; it does not identify the
recursive tensor basis with the separate concrete Hestenes basis.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterCoordinateVectorActionBridge

open Matrix
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge

abbrev TowerSpinor32 := Idx 5 → ℝ
abbrev CoordinateSpinor32 := Fin 32 → ℝ

noncomputable def towerToCoordinateVector :
    TowerSpinor32 ≃ₗ[ℝ] CoordinateSpinor32 :=
  LinearEquiv.funCongrLeft ℝ ℝ towerIndexEquivFin32.symm

theorem towerToCoordinateVector_apply (v : TowerSpinor32) (i : Fin 32) :
    towerToCoordinateVector v i =
      v (towerIndexEquivFin32.symm i) := rfl

theorem towerMatrixReindex_mulVec (A : TowerMat32) (v : TowerSpinor32) :
    towerToCoordinateVector (Matrix.mulVec A v) =
      Matrix.mulVec (towerMatrixReindex A)
        (towerToCoordinateVector v) := by
  change towerToCoordinateVector (Matrix.mulVecLin A v) =
    (Matrix.reindex towerIndexEquivFin32 towerIndexEquivFin32 A).mulVecLin
      (towerToCoordinateVector v)
  rw [Matrix.mulVecLin_reindex]
  change towerToCoordinateVector (Matrix.mulVecLin A v) =
    (LinearEquiv.funCongrLeft ℝ ℝ towerIndexEquivFin32.symm)
      (Matrix.mulVecLin A
        ((LinearEquiv.funCongrLeft ℝ ℝ towerIndexEquivFin32)
          (towerToCoordinateVector v)))
  have hv :
      (LinearEquiv.funCongrLeft ℝ ℝ towerIndexEquivFin32)
          (towerToCoordinateVector v) = v := by
    ext i
    simp [towerToCoordinateVector]
  rw [hv]
  rfl

theorem masterHodgeDirac_vector_intertwine
    (v : TowerSpinor32) :
    towerToCoordinateVector
        (Matrix.mulVec embeddedSplitOctonionHodgeDirac v) =
      Matrix.mulVec masterHodgeDiracFin32
        (towerToCoordinateVector v) := by
  exact towerMatrixReindex_mulVec embeddedSplitOctonionHodgeDirac v

theorem masterChirality_vector_intertwine
    (v : TowerSpinor32) :
    towerToCoordinateVector (Matrix.mulVec MasterChirality v) =
      Matrix.mulVec masterChiralityFin32
        (towerToCoordinateVector v) := by
  exact towerMatrixReindex_mulVec MasterChirality v

end InfoGeometry.Canonical.Cl55MasterCoordinateVectorActionBridge
