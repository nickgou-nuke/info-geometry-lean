import InfoGeometry.Canonical.Cl55MasterCoordinateVectorActionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HodgeFockEmbeddingBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge

/-!
# Explicit pair-coordinate transport for the master `Cl(5,5)` carrier

The concrete Fock realization uses the pair index `Fin 8 × Fin 4`.  This
owner composes the master `Idx 5 ≃ Fin 32` reindexing with the existing
`fin32Equiv`.  It records a basis transport, not an equality of the two
noncomputable basis choices.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterPairCoordinateActionBridge

open Matrix
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.HodgeFockEmbeddingBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge

abbrev PairSpinor32 := (Fin 8 × Fin 4) → ℝ
abbrev PairMatrix32 := Matrix (Fin 8 × Fin 4) (Fin 8 × Fin 4) ℝ

noncomputable def masterIndexEquivPair : Idx 5 ≃ (Fin 8 × Fin 4) :=
  towerIndexEquivFin32.trans fin32Equiv

noncomputable def towerToPairVector :
    (Idx 5 → ℝ) ≃ₗ[ℝ] PairSpinor32 :=
  LinearEquiv.funCongrLeft ℝ ℝ masterIndexEquivPair.symm

noncomputable def towerMatrixReindexPair :
    TowerMat32 ≃ₐ[ℝ] PairMatrix32 :=
  Matrix.reindexAlgEquiv ℝ ℝ masterIndexEquivPair

theorem towerToPairVector_apply (v : Idx 5 → ℝ) (p : Fin 8 × Fin 4) :
    towerToPairVector v p = v (masterIndexEquivPair.symm p) := rfl

theorem towerMatrixReindexPair_mulVec (A : TowerMat32) (v : Idx 5 → ℝ) :
    towerToPairVector (Matrix.mulVec A v) =
      Matrix.mulVec (towerMatrixReindexPair A)
        (towerToPairVector v) := by
  change towerToPairVector (Matrix.mulVecLin A v) =
    (Matrix.reindex masterIndexEquivPair masterIndexEquivPair A).mulVecLin
      (towerToPairVector v)
  rw [Matrix.mulVecLin_reindex]
  change towerToPairVector (Matrix.mulVecLin A v) =
    (LinearEquiv.funCongrLeft ℝ ℝ masterIndexEquivPair.symm)
      (Matrix.mulVecLin A
        ((LinearEquiv.funCongrLeft ℝ ℝ masterIndexEquivPair)
          (towerToPairVector v)))
  have hv :
      (LinearEquiv.funCongrLeft ℝ ℝ masterIndexEquivPair)
          (towerToPairVector v) = v := by
    ext i
    simp [towerToPairVector]
  rw [hv]
  rfl

theorem masterHodgeDirac_pair_vector_intertwine
    (v : Idx 5 → ℝ) :
    towerToPairVector
        (Matrix.mulVec embeddedSplitOctonionHodgeDirac v) =
      Matrix.mulVec (towerMatrixReindexPair
        embeddedSplitOctonionHodgeDirac)
        (towerToPairVector v) := by
  exact towerMatrixReindexPair_mulVec embeddedSplitOctonionHodgeDirac v

/-!
The pair-coordinate matrix inherits the algebraic Hodge packet by transport
through `towerMatrixReindexPair`.  These statements concern the reindexed
master carrier only; they do not identify it with a separately chosen
concrete `dirac32` basis.
-/

noncomputable def masterChiralityPair : PairMatrix32 :=
  towerMatrixReindexPair MasterChirality

noncomputable def masterHodgeDiracPair : PairMatrix32 :=
  towerMatrixReindexPair embeddedSplitOctonionHodgeDirac

theorem masterChiralityPair_anticomm_hodge :
    masterChiralityPair * masterHodgeDiracPair +
        masterHodgeDiracPair * masterChiralityPair = 0 := by
  have h := congrArg towerMatrixReindexPair masterChirality_anticomm_hodge
  simpa [masterChiralityPair, masterHodgeDiracPair, map_mul, map_add] using h

theorem masterHodgeDiracPair_sq :
    masterHodgeDiracPair * masterHodgeDiracPair =
      (3 : ℝ) • (1 : PairMatrix32) := by
  have h := congrArg towerMatrixReindexPair embeddedSplitOctonionHodgeDirac_sq
  simpa [masterHodgeDiracPair, map_mul, map_smul] using h

theorem productMatrixToCoordinate_masterChiralityPair :
    productMatrixToCoordinate masterChiralityPair =
      masterChiralityFin32 := by
  exact productMatrixToCoordinate_reindex MasterChirality

theorem productMatrixToCoordinate_masterHodgeDiracPair :
    productMatrixToCoordinate masterHodgeDiracPair =
      masterHodgeDiracFin32 := by
  exact productMatrixToCoordinate_reindex embeddedSplitOctonionHodgeDirac

end InfoGeometry.Canonical.Cl55MasterPairCoordinateActionBridge
