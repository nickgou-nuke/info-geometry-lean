import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Coordinate transport of the master chiral Hodge blocks

The master chiral calculus is proved on the recursive tensor carrier.  The
concrete Fock embedding uses `Fin 32`; this owner transports the same packet
through the already established matrix algebra equivalence and makes no
additional basis-identification claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterCoordinateChiralBlockBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterCoordinateReindexBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

abbrev CoordinateMat32 := InfoGeometry.Algebra.FiniteSpin.Mat32R

noncomputable def masterChiralProjectorPlusFin32 : CoordinateMat32 :=
  towerMatrixReindex masterChiralProjectorPlus

noncomputable def masterChiralProjectorMinusFin32 : CoordinateMat32 :=
  towerMatrixReindex masterChiralProjectorMinus

noncomputable def masterChiralDiracPlusFin32 : CoordinateMat32 :=
  towerMatrixReindex masterChiralDiracPlus

noncomputable def masterChiralDiracMinusFin32 : CoordinateMat32 :=
  towerMatrixReindex masterChiralDiracMinus

theorem masterChiralProjectorPlusFin32_sq :
    masterChiralProjectorPlusFin32 * masterChiralProjectorPlusFin32 =
      masterChiralProjectorPlusFin32 := by
  have h := congrArg towerMatrixReindex masterChiralProjectorPlus_sq
  simpa [masterChiralProjectorPlusFin32, map_mul] using h

theorem masterChiralProjectorMinusFin32_sq :
    masterChiralProjectorMinusFin32 * masterChiralProjectorMinusFin32 =
      masterChiralProjectorMinusFin32 := by
  have h := congrArg towerMatrixReindex masterChiralProjectorMinus_sq
  simpa [masterChiralProjectorMinusFin32, map_mul] using h

theorem masterChiralProjectorsFin32_orthogonal :
    masterChiralProjectorPlusFin32 * masterChiralProjectorMinusFin32 = 0 ∧
      masterChiralProjectorMinusFin32 * masterChiralProjectorPlusFin32 = 0 := by
  constructor
  · have h := congrArg towerMatrixReindex
      masterChiralProjectors_orthogonal.1
    simpa [masterChiralProjectorPlusFin32,
      masterChiralProjectorMinusFin32, map_mul, map_zero] using h
  · have h := congrArg towerMatrixReindex
      masterChiralProjectors_orthogonal.2
    simpa [masterChiralProjectorPlusFin32,
      masterChiralProjectorMinusFin32, map_mul, map_zero] using h

theorem masterChiralProjectorsFin32_sum :
    masterChiralProjectorPlusFin32 + masterChiralProjectorMinusFin32 = 1 := by
  have h := congrArg towerMatrixReindex masterChiralProjectors_sum
  simpa [masterChiralProjectorPlusFin32,
    masterChiralProjectorMinusFin32, map_add, map_one] using h

theorem masterHodgeDiracFin32_comp_projectorPlus :
    masterHodgeDiracFin32 * masterChiralProjectorPlusFin32 =
      masterChiralProjectorMinusFin32 * masterHodgeDiracFin32 := by
  have h := congrArg towerMatrixReindex masterHodgeDirac_comp_projectorPlus
  simpa [masterHodgeDiracFin32, masterChiralProjectorPlusFin32,
    masterChiralProjectorMinusFin32, map_mul] using h

theorem masterHodgeDiracFin32_comp_projectorMinus :
    masterHodgeDiracFin32 * masterChiralProjectorMinusFin32 =
      masterChiralProjectorPlusFin32 * masterHodgeDiracFin32 := by
  have h := congrArg towerMatrixReindex masterHodgeDirac_comp_projectorMinus
  simpa [masterHodgeDiracFin32, masterChiralProjectorPlusFin32,
    masterChiralProjectorMinusFin32, map_mul] using h

theorem masterChiralDiracPlusFin32_sq_zero :
    masterChiralDiracPlusFin32 * masterChiralDiracPlusFin32 = 0 := by
  have h := congrArg towerMatrixReindex masterChiralDiracPlus_sq_zero
  simpa [masterChiralDiracPlusFin32, map_mul, map_zero] using h

theorem masterChiralDiracMinusFin32_sq_zero :
    masterChiralDiracMinusFin32 * masterChiralDiracMinusFin32 = 0 := by
  have h := congrArg towerMatrixReindex masterChiralDiracMinus_sq_zero
  simpa [masterChiralDiracMinusFin32, map_mul, map_zero] using h

theorem masterChiralDiracFin32_decomposition :
    masterChiralDiracPlusFin32 + masterChiralDiracMinusFin32 =
      masterHodgeDiracFin32 := by
  have h := congrArg towerMatrixReindex masterChiralDirac_decomposition
  simpa [masterChiralDiracPlusFin32, masterChiralDiracMinusFin32,
    masterHodgeDiracFin32, map_add] using h

end InfoGeometry.Canonical.Cl55MasterCoordinateChiralBlockBridge
