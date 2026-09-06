import InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

/-!
# Peirce-defect parity on the finite Witt coordinate carrier

This owner formalizes the finite coordinate readout of the Peirce defect.  It
does not identify that readout with regular left/right multiplication in the
nonassociative split-octonion algebra; such an identification requires a
separate multiplication-table owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionPeirceFermionParityBridge

open InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge
open Matrix

abbrev Mat8 := InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge.Mat8

def peirceDefectSign : Fin 8 → ℝ :=
  ![0, 1, 1, 1, 0, -1, -1, -1]

def peirceDefectMat : Mat8 := Matrix.diagonal peirceDefectSign

def peirceFermionNumberMat : Mat8 := peirceDefectMat * peirceDefectMat

def zeroModeProjectorMat : Mat8 := 1 - peirceFermionNumberMat

def peirceParityMat : Mat8 := 1 - (2 : ℝ) • peirceFermionNumberMat

theorem peirceDefectMat_tripotent :
    peirceDefectMat * peirceDefectMat * peirceDefectMat = peirceDefectMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceDefectMat, peirceDefectSign, Matrix.mul_apply,
      Fin.sum_univ_eight]

theorem peirceFermionNumberMat_idempotent :
    peirceFermionNumberMat * peirceFermionNumberMat = peirceFermionNumberMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceFermionNumberMat, peirceDefectMat, peirceDefectSign,
      Matrix.mul_apply, Fin.sum_univ_eight]

theorem peirceFermionNumberMat_eq_transverseProjector :
    peirceFermionNumberMat = transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceFermionNumberMat, peirceDefectMat, peirceDefectSign,
      transverseProjectorMat, Matrix.mul_apply, Fin.sum_univ_eight]

theorem zeroModeProjectorMat_eq_longitudinalProjector :
    zeroModeProjectorMat = longitudinalProjectorMat := by
  rw [zeroModeProjectorMat, peirceFermionNumberMat_eq_transverseProjector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat,
      Matrix.sub_apply]

theorem peirceParityMat_eq_middleSign :
    peirceParityMat = longitudinalTransverseMat := by
  rw [peirceParityMat, peirceFermionNumberMat_eq_transverseProjector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalTransverseMat, transverseProjectorMat,
      Matrix.sub_apply] <;> norm_num

/-- The combined Cayley--Hestenes square is exactly the Peirce parity matrix. -/
theorem sectorwiseCayley_wittHestenes_square_eq_peirceParity :
    (sectorwiseCayleyMat * wittHestenesMat) *
        (sectorwiseCayleyMat * wittHestenesMat) = peirceParityMat := by
  rw [sectorwiseCayley_wittHestenes_square_eq_grading,
    peirceParityMat_eq_middleSign]

theorem peirceParityMat_eq_two_zeroMode_sub_one :
    peirceParityMat = (2 : ℝ) • zeroModeProjectorMat - 1 := by
  rw [peirceParityMat, zeroModeProjectorMat]
  module

theorem peirceParityMat_wittHestenes_twist :
    sectorwiseCayleyMat * wittHestenesMat =
      -peirceParityMat * wittHestenesMat * sectorwiseCayleyMat := by
  rw [peirceParityMat_eq_middleSign]
  calc
    sectorwiseCayleyMat * wittHestenesMat =
        (sectorwiseCayleyMat * wittHestenesMat) *
          (sectorwiseCayleyMat * sectorwiseCayleyMat) := by
      rw [sectorwiseCayleyMat_sq, mul_one]
    _ = (sectorwiseCayleyMat * wittHestenesMat *
          sectorwiseCayleyMat) * sectorwiseCayleyMat := by
      simp only [mul_assoc]
    _ = (-(longitudinalTransverseMat * wittHestenesMat)) *
        sectorwiseCayleyMat := by
      rw [sectorwiseCayleyMat_wittHestenes_sector_twist]
    _ = -longitudinalTransverseMat * wittHestenesMat *
        sectorwiseCayleyMat := by noncomm_ring

end InfoGeometry.Canonical.SplitOctonionPeirceFermionParityBridge
