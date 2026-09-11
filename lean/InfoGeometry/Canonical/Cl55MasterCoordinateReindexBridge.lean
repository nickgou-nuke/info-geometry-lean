import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HodgeFockEmbeddingBridge

/-!
# Coordinate reindexing for the `Cl(5,5)` master packet

The master CAR owner uses the recursive tensor index `Idx 5`, while the
concrete Fock embedding uses `Fin 32`.  This file provides the explicit native
matrix-algebra reindexing between those carriers.  It does not identify this
reindexing with the separate arithmetic `fin32Equiv`; that comparison remains
a distinct basis-convention theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

abbrev TowerMat32 := Mat32
abbrev CoordinateMat32 := InfoGeometry.Algebra.FiniteSpin.Mat32R
abbrev ProductMat32 := Matrix (Fin 8 × Fin 4) (Fin 8 × Fin 4) ℝ

noncomputable def towerIndexEquivFin32 : Idx 5 ≃ Fin 32 :=
  idxEquivFinPowTwo 5

/-!
The following equivalence makes the two finite index conventions explicit.
It is a genuine change of coordinates, not an identification of the two
underlying basis enumerations.
-/
noncomputable def towerIndexEquivProduct : Idx 5 ≃ Fin 8 × Fin 4 :=
  towerIndexEquivFin32.trans
    InfoGeometry.Canonical.HodgeFockEmbeddingBridge.fin32Equiv

noncomputable def productMatrixReindex (A : TowerMat32) : ProductMat32 :=
  Matrix.reindex towerIndexEquivProduct towerIndexEquivProduct A

noncomputable def productMatrixToCoordinate (B : ProductMat32) : CoordinateMat32 :=
  Matrix.reindex
    InfoGeometry.Canonical.HodgeFockEmbeddingBridge.fin32Equiv.symm
    InfoGeometry.Canonical.HodgeFockEmbeddingBridge.fin32Equiv.symm B

noncomputable def towerMatrixReindex :
    TowerMat32 ≃ₐ[ℝ] CoordinateMat32 :=
  Matrix.reindexAlgEquiv ℝ ℝ towerIndexEquivFin32

theorem productMatrixToCoordinate_reindex (A : TowerMat32) :
    productMatrixToCoordinate (productMatrixReindex A) =
      towerMatrixReindex A := by
  ext i j
  simp [productMatrixToCoordinate, productMatrixReindex,
    towerIndexEquivProduct, towerMatrixReindex]

noncomputable def masterChiralityFin32 : CoordinateMat32 :=
  towerMatrixReindex MasterChirality

noncomputable def masterHodgeDiracFin32 : CoordinateMat32 :=
  towerMatrixReindex embeddedSplitOctonionHodgeDirac

theorem masterChiralityFin32_sq :
    masterChiralityFin32 * masterChiralityFin32 = 1 := by
  have h := congrArg towerMatrixReindex masterChirality_sq
  simpa [masterChiralityFin32, map_mul] using h

theorem masterChiralityFin32_anticomm_hodge :
    masterChiralityFin32 * masterHodgeDiracFin32 +
        masterHodgeDiracFin32 * masterChiralityFin32 = 0 := by
  have h := congrArg towerMatrixReindex masterChirality_anticomm_hodge
  simpa [masterChiralityFin32, masterHodgeDiracFin32, map_mul,
    map_add] using h

theorem masterHodgeDiracFin32_sq :
    masterHodgeDiracFin32 * masterHodgeDiracFin32 =
      (3 : ℝ) • (1 : CoordinateMat32) := by
  have h := congrArg towerMatrixReindex embeddedSplitOctonionHodgeDirac_sq
  simpa [masterHodgeDiracFin32, map_mul, map_smul] using h

theorem masterChiralityFin32_commutes_inducedEvenMomentum :
    masterChiralityFin32 * towerMatrixReindex inducedEvenMomentum =
      towerMatrixReindex inducedEvenMomentum * masterChiralityFin32 := by
  have h := congrArg towerMatrixReindex
    masterChirality_commutes_inducedEvenMomentum
  simpa [masterChiralityFin32, map_mul] using h

end InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
