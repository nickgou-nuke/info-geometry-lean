import InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hypercomplex structure on the four Witt planes

The `Mat8` carrier has four Witt pairs in the order
`(u₊, σ₁⁺, σ₂⁺, σ₃⁺, u₋, σ₁⁻, σ₂⁻, σ₃⁻)`.
This owner separates the longitudinal pair `(u₊,u₋)` from the three
transverse pairs.  It constructs the real operator `K = S P`, where `P` is
the Peirce grading and `S` is the chiral exchange.  Thus `K² = -I` follows
from the already proved anticommutation `S P = - P S`.

The boost and phase expressions below are algebraic polynomial combinations
of these finite matrices.  They are not asserted to be Tomita modular flows
or analytic exponentials.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

open InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge
open Matrix

abbrev Mat8 := InfoGeometry.Lie.SplitOctonionExteriorAlgebraPeirceBridge.Mat8

/-- `+1` on the longitudinal Witt pair and `-1` on the three transverse
Witt pairs.  This is a grading involution, not yet a Krein fundamental
symmetry. -/
def longitudinalTransverseMat : Mat8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1]]

/-- Intrinsic Witt Hestenes matrix: product of Peirce grading and exchange involution. -/
def wittHestenesMat : Mat8 :=
  peirceGradingMat * exchangeInvolutionMat

def longitudinalProjectorMat : Mat8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

def transverseProjectorMat : Mat8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

def longitudinalBoostGeneratorMat : Mat8 :=
  peirceGradingMat * longitudinalProjectorMat

def transverseHestenesMat : Mat8 :=
  wittHestenesMat * transverseProjectorMat

/-- The sectorwise Cayley readout: exchange on the longitudinal pair and
minus the identity on the transverse sector.  Its identification with the
coordinate-level Cayley map is a separate intertwining theorem. -/
def sectorwiseCayleyMat : Mat8 :=
  exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat

theorem longitudinal_transverse_projectors_orthogonal :
    longitudinalProjectorMat * transverseProjectorMat = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat, Fin.sum_univ_eight]

theorem transverse_longitudinal_projectors_orthogonal :
    transverseProjectorMat * longitudinalProjectorMat = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat, Fin.sum_univ_eight]

theorem longitudinal_transverse_projectors_complete :
    longitudinalProjectorMat + transverseProjectorMat = 1 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat]

theorem longitudinalTransverseMat_eq_sub_projectors :
    longitudinalTransverseMat = longitudinalProjectorMat - transverseProjectorMat := by
  ext i j
  simp only [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalTransverseMat, longitudinalProjectorMat, transverseProjectorMat]

theorem peirce_comm_longitudinalProjectorMat :
    peirceGradingMat * longitudinalProjectorMat =
      longitudinalProjectorMat * peirceGradingMat := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [peirceGradingMat, longitudinalProjectorMat, Fin.sum_univ_eight]

theorem peirce_comm_transverseProjectorMat :
    peirceGradingMat * transverseProjectorMat =
      transverseProjectorMat * peirceGradingMat := by
  have hcomp : transverseProjectorMat = 1 - longitudinalProjectorMat := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      simp [longitudinalProjectorMat, transverseProjectorMat]
  rw [hcomp, mul_sub, sub_mul, mul_one, one_mul, peirce_comm_longitudinalProjectorMat]

theorem exchange_comm_longitudinalProjectorMat :
    exchangeInvolutionMat * longitudinalProjectorMat =
      longitudinalProjectorMat * exchangeInvolutionMat := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, exchangeInvolutionMat, Fin.sum_univ_eight]

theorem exchange_comm_transverseProjectorMat :
    exchangeInvolutionMat * transverseProjectorMat =
      transverseProjectorMat * exchangeInvolutionMat := by
  have hcomp : transverseProjectorMat = 1 - longitudinalProjectorMat := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      simp [longitudinalProjectorMat, transverseProjectorMat]
  rw [hcomp, mul_sub, sub_mul, mul_one, one_mul, exchange_comm_longitudinalProjectorMat]

theorem exchange_peirceGrading_anticomm_product :
    exchangeInvolutionMat * peirceGradingMat = -peirceGradingMat * exchangeInvolutionMat := by
  have h := exchange_peirceGrading_anticomm
  calc exchangeInvolutionMat * peirceGradingMat
    _ = (exchangeInvolutionMat * peirceGradingMat * exchangeInvolutionMat) * exchangeInvolutionMat := by
          rw [mul_assoc, exchangeInvolutionMat_sq, mul_one]
    _ = -peirceGradingMat * exchangeInvolutionMat := by rw [h]

theorem wittHestenesMat_comm_longitudinalProjectorMat :
    wittHestenesMat * longitudinalProjectorMat =
      longitudinalProjectorMat * wittHestenesMat := by
  calc wittHestenesMat * longitudinalProjectorMat
    _ = (peirceGradingMat * exchangeInvolutionMat) * longitudinalProjectorMat := rfl
    _ = peirceGradingMat * (exchangeInvolutionMat * longitudinalProjectorMat) := by rw [mul_assoc]
    _ = peirceGradingMat * (longitudinalProjectorMat * exchangeInvolutionMat) := by
          rw [exchange_comm_longitudinalProjectorMat]
    _ = (peirceGradingMat * longitudinalProjectorMat) * exchangeInvolutionMat := by rw [← mul_assoc]
    _ = (longitudinalProjectorMat * peirceGradingMat) * exchangeInvolutionMat := by
          rw [peirce_comm_longitudinalProjectorMat]
    _ = longitudinalProjectorMat * (peirceGradingMat * exchangeInvolutionMat) := by rw [mul_assoc]
    _ = longitudinalProjectorMat * wittHestenesMat := rfl

theorem wittHestenesMat_comm_transverseProjectorMat :
    wittHestenesMat * transverseProjectorMat =
      transverseProjectorMat * wittHestenesMat := by
  calc wittHestenesMat * transverseProjectorMat
    _ = (peirceGradingMat * exchangeInvolutionMat) * transverseProjectorMat := rfl
    _ = peirceGradingMat * (exchangeInvolutionMat * transverseProjectorMat) := by rw [mul_assoc]
    _ = peirceGradingMat * (transverseProjectorMat * exchangeInvolutionMat) := by
          rw [exchange_comm_transverseProjectorMat]
    _ = (peirceGradingMat * transverseProjectorMat) * exchangeInvolutionMat := by rw [← mul_assoc]
    _ = (transverseProjectorMat * peirceGradingMat) * exchangeInvolutionMat := by
          rw [peirce_comm_transverseProjectorMat]
    _ = transverseProjectorMat * (peirceGradingMat * exchangeInvolutionMat) := by rw [mul_assoc]
    _ = transverseProjectorMat * wittHestenesMat := rfl

theorem longitudinalTransverseMat_comm_peirce :
    longitudinalTransverseMat * peirceGradingMat =
      peirceGradingMat * longitudinalTransverseMat := by
  rw [longitudinalTransverseMat_eq_sub_projectors, sub_mul, mul_sub,
      peirce_comm_longitudinalProjectorMat, peirce_comm_transverseProjectorMat]

theorem longitudinalTransverseMat_comm_exchange :
    longitudinalTransverseMat * exchangeInvolutionMat =
      exchangeInvolutionMat * longitudinalTransverseMat := by
  rw [longitudinalTransverseMat_eq_sub_projectors, sub_mul, mul_sub,
      exchange_comm_longitudinalProjectorMat, exchange_comm_transverseProjectorMat]

theorem longitudinalTransverseMat_comm_wittHestenes :
    longitudinalTransverseMat * wittHestenesMat =
      wittHestenesMat * longitudinalTransverseMat := by
  rw [longitudinalTransverseMat_eq_sub_projectors, sub_mul, mul_sub,
      wittHestenesMat_comm_longitudinalProjectorMat,
      wittHestenesMat_comm_transverseProjectorMat]

@[simp] theorem longitudinalProjectorMat_sq :
    longitudinalProjectorMat * longitudinalProjectorMat =
      longitudinalProjectorMat := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, Fin.sum_univ_eight]

@[simp] theorem transverseProjectorMat_sq :
    transverseProjectorMat * transverseProjectorMat =
      transverseProjectorMat := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [transverseProjectorMat, Fin.sum_univ_eight]

@[simp] theorem longitudinalTransverseMat_sq :
    longitudinalTransverseMat * longitudinalTransverseMat = 1 := by
  calc longitudinalTransverseMat * longitudinalTransverseMat
    _ = (longitudinalProjectorMat - transverseProjectorMat) *
          (longitudinalProjectorMat - transverseProjectorMat) := by
          rw [longitudinalTransverseMat_eq_sub_projectors]
    _ = longitudinalProjectorMat * longitudinalProjectorMat -
        longitudinalProjectorMat * transverseProjectorMat -
        transverseProjectorMat * longitudinalProjectorMat +
        transverseProjectorMat * transverseProjectorMat := by
          noncomm_ring
    _ = longitudinalProjectorMat - 0 - 0 + transverseProjectorMat := by
          rw [longitudinalProjectorMat_sq, transverseProjectorMat_sq,
              longitudinal_transverse_projectors_orthogonal,
              transverse_longitudinal_projectors_orthogonal]
    _ = longitudinalProjectorMat + transverseProjectorMat := by
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
          ring
    _ = 1 := longitudinal_transverse_projectors_complete

@[simp] theorem wittHestenesMat_sq :
    wittHestenesMat * wittHestenesMat = -1 := by
  calc wittHestenesMat * wittHestenesMat
    _ = (peirceGradingMat * exchangeInvolutionMat) * (peirceGradingMat * exchangeInvolutionMat) := by rfl
    _ = peirceGradingMat * (exchangeInvolutionMat * peirceGradingMat) * exchangeInvolutionMat := by
          simp only [mul_assoc]
    _ = peirceGradingMat * (-peirceGradingMat * exchangeInvolutionMat) * exchangeInvolutionMat := by
          rw [exchange_peirceGrading_anticomm_product]
    _ = -(peirceGradingMat * peirceGradingMat) * (exchangeInvolutionMat * exchangeInvolutionMat) := by
          noncomm_ring
    _ = -1 * 1 := by rw [peirceGradingMat_sq, exchangeInvolutionMat_sq]
    _ = -1 := by rw [mul_one]

@[simp] theorem longitudinalBoostGeneratorMat_sq :
    longitudinalBoostGeneratorMat * longitudinalBoostGeneratorMat =
      longitudinalProjectorMat := by
  calc longitudinalBoostGeneratorMat * longitudinalBoostGeneratorMat
    _ = (peirceGradingMat * longitudinalProjectorMat) *
          (peirceGradingMat * longitudinalProjectorMat) := rfl
    _ = peirceGradingMat * (longitudinalProjectorMat * peirceGradingMat) *
          longitudinalProjectorMat := by simp only [mul_assoc]
    _ = peirceGradingMat * (peirceGradingMat * longitudinalProjectorMat) *
          longitudinalProjectorMat := by rw [peirce_comm_longitudinalProjectorMat]
    _ = (peirceGradingMat * peirceGradingMat) *
          (longitudinalProjectorMat * longitudinalProjectorMat) := by noncomm_ring
    _ = 1 * longitudinalProjectorMat := by rw [peirceGradingMat_sq, longitudinalProjectorMat_sq]
    _ = longitudinalProjectorMat := by rw [one_mul]

@[simp] theorem transverseHestenesMat_sq :
    transverseHestenesMat * transverseHestenesMat =
      -transverseProjectorMat := by
  calc transverseHestenesMat * transverseHestenesMat
    _ = (wittHestenesMat * transverseProjectorMat) *
          (wittHestenesMat * transverseProjectorMat) := rfl
    _ = wittHestenesMat * (transverseProjectorMat * wittHestenesMat) *
          transverseProjectorMat := by simp only [mul_assoc]
    _ = wittHestenesMat * (wittHestenesMat * transverseProjectorMat) *
          transverseProjectorMat := by rw [wittHestenesMat_comm_transverseProjectorMat]
    _ = (wittHestenesMat * wittHestenesMat) *
          (transverseProjectorMat * transverseProjectorMat) := by noncomm_ring
    _ = -1 * transverseProjectorMat := by rw [wittHestenesMat_sq, transverseProjectorMat_sq]
    _ = -transverseProjectorMat := by rw [neg_one_mul]

theorem sectorwiseCayleyMat_on_longitudinal :
    sectorwiseCayleyMat * longitudinalProjectorMat =
      exchangeInvolutionMat * longitudinalProjectorMat := by
  calc sectorwiseCayleyMat * longitudinalProjectorMat
    _ = (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) *
          longitudinalProjectorMat := by rw [sectorwiseCayleyMat]
    _ = exchangeInvolutionMat * (longitudinalProjectorMat * longitudinalProjectorMat) -
          transverseProjectorMat * longitudinalProjectorMat := by
            simp only [sub_mul, mul_assoc]
    _ = exchangeInvolutionMat * longitudinalProjectorMat - 0 := by
            rw [longitudinalProjectorMat_sq, transverse_longitudinal_projectors_orthogonal]
    _ = exchangeInvolutionMat * longitudinalProjectorMat := by rw [sub_zero]

theorem sectorwiseCayleyMat_on_transverse :
    sectorwiseCayleyMat * transverseProjectorMat =
      -transverseProjectorMat := by
  calc sectorwiseCayleyMat * transverseProjectorMat
    _ = (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) *
          transverseProjectorMat := by rw [sectorwiseCayleyMat]
    _ = exchangeInvolutionMat * (longitudinalProjectorMat * transverseProjectorMat) -
          transverseProjectorMat * transverseProjectorMat := by
            simp only [sub_mul, mul_assoc]
    _ = exchangeInvolutionMat * 0 - transverseProjectorMat := by
            rw [longitudinal_transverse_projectors_orthogonal, transverseProjectorMat_sq]
    _ = -transverseProjectorMat := by rw [mul_zero, zero_sub]

theorem longitudinal_on_sectorwiseCayleyMat :
    longitudinalProjectorMat * sectorwiseCayleyMat =
      longitudinalProjectorMat * exchangeInvolutionMat := by
  calc longitudinalProjectorMat * sectorwiseCayleyMat
    _ = longitudinalProjectorMat *
          (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) := by
            rw [sectorwiseCayleyMat]
    _ = longitudinalProjectorMat * (exchangeInvolutionMat * longitudinalProjectorMat) -
          longitudinalProjectorMat * transverseProjectorMat := by
            simp only [mul_sub]
    _ = longitudinalProjectorMat * (longitudinalProjectorMat * exchangeInvolutionMat) - 0 := by
            rw [exchange_comm_longitudinalProjectorMat, longitudinal_transverse_projectors_orthogonal]
    _ = (longitudinalProjectorMat * longitudinalProjectorMat) * exchangeInvolutionMat := by
            rw [sub_zero, mul_assoc]
    _ = longitudinalProjectorMat * exchangeInvolutionMat := by
            rw [longitudinalProjectorMat_sq]

theorem transverse_on_sectorwiseCayleyMat :
    transverseProjectorMat * sectorwiseCayleyMat =
      -transverseProjectorMat := by
  calc transverseProjectorMat * sectorwiseCayleyMat
    _ = transverseProjectorMat *
          (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) := by
            rw [sectorwiseCayleyMat]
    _ = transverseProjectorMat * (exchangeInvolutionMat * longitudinalProjectorMat) -
          transverseProjectorMat * transverseProjectorMat := by
            simp only [mul_sub]
    _ = transverseProjectorMat * (longitudinalProjectorMat * exchangeInvolutionMat) -
          transverseProjectorMat := by
            rw [exchange_comm_longitudinalProjectorMat, transverseProjectorMat_sq]
    _ = (transverseProjectorMat * longitudinalProjectorMat) * exchangeInvolutionMat -
          transverseProjectorMat := by
            rw [mul_assoc]
    _ = 0 * exchangeInvolutionMat - transverseProjectorMat := by
            rw [transverse_longitudinal_projectors_orthogonal]
    _ = -transverseProjectorMat := by
            rw [zero_mul, zero_sub]

@[simp] theorem sectorwiseCayleyMat_sq :
    sectorwiseCayleyMat * sectorwiseCayleyMat = 1 := by
  calc sectorwiseCayleyMat * sectorwiseCayleyMat
    _ = sectorwiseCayleyMat * (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) := by
          rw [sectorwiseCayleyMat]
    _ = sectorwiseCayleyMat * (longitudinalProjectorMat * exchangeInvolutionMat) -
          sectorwiseCayleyMat * transverseProjectorMat := by
          rw [← exchange_comm_longitudinalProjectorMat, mul_sub]
    _ = (sectorwiseCayleyMat * longitudinalProjectorMat) * exchangeInvolutionMat -
          (-transverseProjectorMat) := by
          rw [mul_assoc, sectorwiseCayleyMat_on_transverse]
    _ = (exchangeInvolutionMat * longitudinalProjectorMat) * exchangeInvolutionMat +
          transverseProjectorMat := by
          rw [sectorwiseCayleyMat_on_longitudinal, sub_neg_eq_add]
    _ = (longitudinalProjectorMat * exchangeInvolutionMat) * exchangeInvolutionMat +
          transverseProjectorMat := by
          rw [← exchange_comm_longitudinalProjectorMat]
    _ = longitudinalProjectorMat * (exchangeInvolutionMat * exchangeInvolutionMat) +
          transverseProjectorMat := by
          rw [mul_assoc]
    _ = longitudinalProjectorMat * 1 + transverseProjectorMat := by
          rw [exchangeInvolutionMat_sq]
    _ = longitudinalProjectorMat + transverseProjectorMat := by
          rw [mul_one]
    _ = 1 := longitudinal_transverse_projectors_complete

theorem sectorwiseCayleyMat_comm_longitudinalTransverse :
    sectorwiseCayleyMat * longitudinalTransverseMat =
      longitudinalTransverseMat * sectorwiseCayleyMat := by
  calc sectorwiseCayleyMat * longitudinalTransverseMat
    _ = sectorwiseCayleyMat * (longitudinalProjectorMat - transverseProjectorMat) := by
          rw [longitudinalTransverseMat_eq_sub_projectors]
    _ = sectorwiseCayleyMat * longitudinalProjectorMat -
        sectorwiseCayleyMat * transverseProjectorMat := by rw [mul_sub]
    _ = exchangeInvolutionMat * longitudinalProjectorMat - (-transverseProjectorMat) := by
          rw [sectorwiseCayleyMat_on_longitudinal, sectorwiseCayleyMat_on_transverse]
    _ = longitudinalProjectorMat * exchangeInvolutionMat - (-transverseProjectorMat) := by
          rw [exchange_comm_longitudinalProjectorMat]
    _ = longitudinalProjectorMat * sectorwiseCayleyMat -
        transverseProjectorMat * sectorwiseCayleyMat := by
          rw [longitudinal_on_sectorwiseCayleyMat, transverse_on_sectorwiseCayleyMat]
    _ = (longitudinalProjectorMat - transverseProjectorMat) * sectorwiseCayleyMat := by
          rw [sub_mul]
    _ = longitudinalTransverseMat * sectorwiseCayleyMat := by
          rw [← longitudinalTransverseMat_eq_sub_projectors]

theorem sectorwiseCayleyMat_mul_wittHestenesMat :
    sectorwiseCayleyMat * wittHestenesMat =
      -(longitudinalProjectorMat * peirceGradingMat +
        transverseProjectorMat * wittHestenesMat) := by
  calc sectorwiseCayleyMat * wittHestenesMat
    _ = (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) *
          (peirceGradingMat * exchangeInvolutionMat) := rfl
    _ = exchangeInvolutionMat * longitudinalProjectorMat *
          (peirceGradingMat * exchangeInvolutionMat) -
        transverseProjectorMat * wittHestenesMat := by
          rw [sub_mul]
          rfl
    _ = (exchangeInvolutionMat * (longitudinalProjectorMat * peirceGradingMat)) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          simp only [mul_assoc]
    _ = (exchangeInvolutionMat * (peirceGradingMat * longitudinalProjectorMat)) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          rw [peirce_comm_longitudinalProjectorMat]
    _ = ((exchangeInvolutionMat * peirceGradingMat) * longitudinalProjectorMat) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          rw [← mul_assoc]
    _ = ((-peirceGradingMat * exchangeInvolutionMat) * longitudinalProjectorMat) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          rw [exchange_peirceGrading_anticomm_product]
    _ = -peirceGradingMat * (exchangeInvolutionMat * longitudinalProjectorMat) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          simp only [neg_mul, mul_assoc]
    _ = -peirceGradingMat * (longitudinalProjectorMat * exchangeInvolutionMat) *
          exchangeInvolutionMat - transverseProjectorMat * wittHestenesMat := by
          rw [exchange_comm_longitudinalProjectorMat]
    _ = -peirceGradingMat * longitudinalProjectorMat *
          (exchangeInvolutionMat * exchangeInvolutionMat) -
        transverseProjectorMat * wittHestenesMat := by
          simp only [neg_mul, mul_assoc]
    _ = -peirceGradingMat * longitudinalProjectorMat * 1 -
        transverseProjectorMat * wittHestenesMat := by
          rw [exchangeInvolutionMat_sq]
    _ = -(longitudinalProjectorMat * peirceGradingMat) -
        transverseProjectorMat * wittHestenesMat := by
          rw [mul_one, neg_mul, peirce_comm_longitudinalProjectorMat]
    _ = -(longitudinalProjectorMat * peirceGradingMat +
        transverseProjectorMat * wittHestenesMat) := by
          rw [sub_eq_add_neg, ← neg_add]

theorem wittHestenesMat_mul_sectorwiseCayleyMat :
    wittHestenesMat * sectorwiseCayleyMat =
      longitudinalProjectorMat * peirceGradingMat -
        transverseProjectorMat * wittHestenesMat := by
  calc wittHestenesMat * sectorwiseCayleyMat
    _ = (peirceGradingMat * exchangeInvolutionMat) *
          (exchangeInvolutionMat * longitudinalProjectorMat - transverseProjectorMat) := rfl
    _ = (peirceGradingMat * exchangeInvolutionMat) *
          (exchangeInvolutionMat * longitudinalProjectorMat) -
        (peirceGradingMat * exchangeInvolutionMat) * transverseProjectorMat := by
          rw [mul_sub]
    _ = peirceGradingMat * (exchangeInvolutionMat * exchangeInvolutionMat) *
          longitudinalProjectorMat -
        peirceGradingMat * (exchangeInvolutionMat * transverseProjectorMat) := by
          simp only [mul_assoc]
    _ = peirceGradingMat * 1 * longitudinalProjectorMat -
        peirceGradingMat * (transverseProjectorMat * exchangeInvolutionMat) := by
          rw [exchangeInvolutionMat_sq, exchange_comm_transverseProjectorMat]
    _ = peirceGradingMat * longitudinalProjectorMat -
        (peirceGradingMat * transverseProjectorMat) * exchangeInvolutionMat := by
          rw [mul_one, mul_assoc]
    _ = longitudinalProjectorMat * peirceGradingMat -
        (transverseProjectorMat * peirceGradingMat) * exchangeInvolutionMat := by
          rw [peirce_comm_longitudinalProjectorMat, peirce_comm_transverseProjectorMat]
    _ = longitudinalProjectorMat * peirceGradingMat -
        transverseProjectorMat * (peirceGradingMat * exchangeInvolutionMat) := by
          rw [mul_assoc]
    _ = longitudinalProjectorMat * peirceGradingMat -
        transverseProjectorMat * wittHestenesMat := rfl

theorem cayley_hestenes_commutator_localized :
    sectorwiseCayleyMat * wittHestenesMat -
        wittHestenesMat * sectorwiseCayleyMat =
      (-2 : ℝ) • (longitudinalProjectorMat * peirceGradingMat) := by
  calc sectorwiseCayleyMat * wittHestenesMat - wittHestenesMat * sectorwiseCayleyMat
    _ = -(longitudinalProjectorMat * peirceGradingMat + transverseProjectorMat * wittHestenesMat) -
        (longitudinalProjectorMat * peirceGradingMat - transverseProjectorMat * wittHestenesMat) := by
          rw [sectorwiseCayleyMat_mul_wittHestenesMat, wittHestenesMat_mul_sectorwiseCayleyMat]
    _ = (-2 : ℝ) • (longitudinalProjectorMat * peirceGradingMat) := by
          ext i j
          simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply]
          ring

theorem cayley_hestenes_anticommutator_localized :
    sectorwiseCayleyMat * wittHestenesMat +
        wittHestenesMat * sectorwiseCayleyMat =
      (-2 : ℝ) • (transverseProjectorMat * wittHestenesMat) := by
  calc sectorwiseCayleyMat * wittHestenesMat + wittHestenesMat * sectorwiseCayleyMat
    _ = -(longitudinalProjectorMat * peirceGradingMat + transverseProjectorMat * wittHestenesMat) +
        (longitudinalProjectorMat * peirceGradingMat - transverseProjectorMat * wittHestenesMat) := by
          rw [sectorwiseCayleyMat_mul_wittHestenesMat, wittHestenesMat_mul_sectorwiseCayleyMat]
    _ = (-2 : ℝ) • (transverseProjectorMat * wittHestenesMat) := by
          ext i j
          simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply]
          ring

theorem sectorwiseCayleyMat_longitudinal_wittHestenes_anticommute :
    (sectorwiseCayleyMat * wittHestenesMat) * longitudinalProjectorMat =
      -((wittHestenesMat * sectorwiseCayleyMat) *
        longitudinalProjectorMat) := by
  have h : (sectorwiseCayleyMat * wittHestenesMat + wittHestenesMat * sectorwiseCayleyMat) *
      longitudinalProjectorMat = 0 := by
    rw [cayley_hestenes_anticommutator_localized, smul_mul_assoc, mul_assoc,
        wittHestenesMat_comm_longitudinalProjectorMat, ← mul_assoc transverseProjectorMat longitudinalProjectorMat,
        transverse_longitudinal_projectors_orthogonal, zero_mul, smul_zero]
  rw [add_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sectorwiseCayleyMat_transverse_wittHestenes_commute :
    (sectorwiseCayleyMat * wittHestenesMat) * transverseProjectorMat =
      (wittHestenesMat * sectorwiseCayleyMat) *
        transverseProjectorMat := by
  have h : (sectorwiseCayleyMat * wittHestenesMat - wittHestenesMat * sectorwiseCayleyMat) *
      transverseProjectorMat = 0 := by
    rw [cayley_hestenes_commutator_localized, smul_mul_assoc, mul_assoc,
        peirce_comm_transverseProjectorMat, ← mul_assoc longitudinalProjectorMat transverseProjectorMat,
        longitudinal_transverse_projectors_orthogonal, zero_mul, smul_zero]
  rw [sub_mul] at h
  exact eq_of_sub_eq_zero h

/-- The global Cayley/Hestenes relation records the opposite signs on the
longitudinal and transverse sectors. -/
theorem sectorwiseCayleyMat_wittHestenes_sector_twist :
    sectorwiseCayleyMat * wittHestenesMat * sectorwiseCayleyMat =
      -(longitudinalTransverseMat * wittHestenesMat) := by
  have hLP_C : longitudinalProjectorMat * peirceGradingMat * sectorwiseCayleyMat =
      longitudinalProjectorMat * wittHestenesMat := by
    calc longitudinalProjectorMat * peirceGradingMat * sectorwiseCayleyMat
      _ = peirceGradingMat * longitudinalProjectorMat * sectorwiseCayleyMat := by
            rw [peirce_comm_longitudinalProjectorMat]
      _ = peirceGradingMat * (longitudinalProjectorMat * sectorwiseCayleyMat) := by
            rw [mul_assoc]
      _ = peirceGradingMat * (longitudinalProjectorMat * exchangeInvolutionMat) := by
            rw [longitudinal_on_sectorwiseCayleyMat]
      _ = (peirceGradingMat * longitudinalProjectorMat) * exchangeInvolutionMat := by
            rw [← mul_assoc]
      _ = (longitudinalProjectorMat * peirceGradingMat) * exchangeInvolutionMat := by
            rw [peirce_comm_longitudinalProjectorMat]
      _ = longitudinalProjectorMat * (peirceGradingMat * exchangeInvolutionMat) := by
            rw [mul_assoc]
      _ = longitudinalProjectorMat * wittHestenesMat := rfl
  calc sectorwiseCayleyMat * wittHestenesMat * sectorwiseCayleyMat
    _ = (sectorwiseCayleyMat * wittHestenesMat) * sectorwiseCayleyMat := by rw [mul_assoc]
    _ = -(longitudinalProjectorMat * peirceGradingMat + transverseProjectorMat * wittHestenesMat) *
          sectorwiseCayleyMat := by rw [sectorwiseCayleyMat_mul_wittHestenesMat]
    _ = -( (longitudinalProjectorMat * peirceGradingMat + transverseProjectorMat * wittHestenesMat) *
          sectorwiseCayleyMat ) := by rw [neg_mul]
    _ = -( longitudinalProjectorMat * peirceGradingMat * sectorwiseCayleyMat +
          transverseProjectorMat * wittHestenesMat * sectorwiseCayleyMat ) := by rw [add_mul]
    _ = -( longitudinalProjectorMat * peirceGradingMat * sectorwiseCayleyMat +
          transverseProjectorMat * (wittHestenesMat * sectorwiseCayleyMat) ) := by
          rw [mul_assoc transverseProjectorMat wittHestenesMat sectorwiseCayleyMat]
    _ = -( longitudinalProjectorMat * wittHestenesMat +
          transverseProjectorMat * (longitudinalProjectorMat * peirceGradingMat -
            transverseProjectorMat * wittHestenesMat) ) := by
          rw [hLP_C, wittHestenesMat_mul_sectorwiseCayleyMat]
    _ = -( longitudinalProjectorMat * wittHestenesMat +
          (transverseProjectorMat * (longitudinalProjectorMat * peirceGradingMat) -
            transverseProjectorMat * (transverseProjectorMat * wittHestenesMat)) ) := by
          rw [mul_sub]
    _ = -( longitudinalProjectorMat * wittHestenesMat +
          (transverseProjectorMat * longitudinalProjectorMat * peirceGradingMat -
            transverseProjectorMat * transverseProjectorMat * wittHestenesMat) ) := by
          simp only [mul_assoc]
    _ = -( longitudinalProjectorMat * wittHestenesMat +
          (0 * peirceGradingMat - transverseProjectorMat * wittHestenesMat) ) := by
          rw [transverse_longitudinal_projectors_orthogonal, transverseProjectorMat_sq]
    _ = -( longitudinalProjectorMat * wittHestenesMat +
          (0 - transverseProjectorMat * wittHestenesMat) ) := by rw [zero_mul]
    _ = -( longitudinalProjectorMat * wittHestenesMat + - (transverseProjectorMat * wittHestenesMat) ) := by
          rw [zero_sub]
    _ = -( longitudinalProjectorMat * wittHestenesMat - transverseProjectorMat * wittHestenesMat ) := by
          rw [← sub_eq_add_neg]
    _ = -( (longitudinalProjectorMat - transverseProjectorMat) * wittHestenesMat ) := by
          rw [sub_mul]
    _ = -( longitudinalTransverseMat * wittHestenesMat ) := by
          rw [← longitudinalTransverseMat_eq_sub_projectors]

theorem sectorwiseCayleyMat_wittHestenes_twisted :
    sectorwiseCayleyMat * wittHestenesMat =
      -(longitudinalTransverseMat * wittHestenesMat *
        sectorwiseCayleyMat) := by
  calc
    sectorwiseCayleyMat * wittHestenesMat =
        (sectorwiseCayleyMat * wittHestenesMat *
          sectorwiseCayleyMat) * sectorwiseCayleyMat := by
      rw [mul_assoc, sectorwiseCayleyMat_sq, mul_one]
    _ = -(longitudinalTransverseMat * wittHestenesMat) *
          sectorwiseCayleyMat := by
      rw [sectorwiseCayleyMat_wittHestenes_sector_twist]
    _ = -(longitudinalTransverseMat * wittHestenesMat *
          sectorwiseCayleyMat) := by
      noncomm_ring

theorem sectorwiseCayley_wittHestenes_square_eq_grading :
    (sectorwiseCayleyMat * wittHestenesMat) *
        (sectorwiseCayleyMat * wittHestenesMat) =
      longitudinalTransverseMat := by
  calc
    (sectorwiseCayleyMat * wittHestenesMat) *
        (sectorwiseCayleyMat * wittHestenesMat) =
        (sectorwiseCayleyMat * wittHestenesMat *
          sectorwiseCayleyMat) * wittHestenesMat := by
      simp only [mul_assoc]
    _ = (-(longitudinalTransverseMat * wittHestenesMat)) *
          wittHestenesMat := by
      rw [sectorwiseCayleyMat_wittHestenes_sector_twist]
    _ = -(longitudinalTransverseMat * (wittHestenesMat * wittHestenesMat)) := by
      noncomm_ring
    _ = -(longitudinalTransverseMat * (-1)) := by
      exact congrArg (fun X => -(longitudinalTransverseMat * X))
        wittHestenesMat_sq
    _ = longitudinalTransverseMat := by
      rw [mul_neg_one, neg_neg]

theorem longitudinalProjectorMat_eq_half_add_grading :
    longitudinalProjectorMat =
      (1 / 2 : ℝ) • (1 + longitudinalTransverseMat) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, longitudinalTransverseMat] <;> norm_num

theorem transverseProjectorMat_eq_half_sub_grading :
    transverseProjectorMat =
      (1 / 2 : ℝ) • (1 - longitudinalTransverseMat) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [transverseProjectorMat, longitudinalTransverseMat] <;> norm_num

theorem sectorwiseCayleyMat_wittHestenes_not_commute :
    sectorwiseCayleyMat * wittHestenesMat ≠
      wittHestenesMat * sectorwiseCayleyMat := by
  intro h
  have hanti := sectorwiseCayleyMat_longitudinal_wittHestenes_anticommute
  have hzero' :
      (wittHestenesMat * sectorwiseCayleyMat) * longitudinalProjectorMat = 0 := by
    rw [h] at hanti
    ext i j
    have hij := congrArg (fun A : Mat8 => A i j) hanti
    dsimp at hij
    have hb :
        ((wittHestenesMat * sectorwiseCayleyMat) *
          longitudinalProjectorMat) i j = 0 := by
      linarith [hij]
    simpa using hb
  have hzero :
      (sectorwiseCayleyMat * wittHestenesMat) * longitudinalProjectorMat = 0 := by
    rw [h]
    exact hzero'
  have hL : longitudinalProjectorMat ≠ 0 := by
    intro hL
    have h00 := congrArg (fun A : Mat8 => A 0 0) hL
    norm_num [longitudinalProjectorMat] at h00
  have hC : sectorwiseCayleyMat * sectorwiseCayleyMat = 1 :=
    sectorwiseCayleyMat_sq
  have hK : wittHestenesMat * wittHestenesMat = -1 :=
    wittHestenesMat_sq
  have hleft :
      (-wittHestenesMat * sectorwiseCayleyMat) *
          ((sectorwiseCayleyMat * wittHestenesMat) *
            longitudinalProjectorMat) = longitudinalProjectorMat := by
    calc
      (-wittHestenesMat * sectorwiseCayleyMat) *
          ((sectorwiseCayleyMat * wittHestenesMat) *
            longitudinalProjectorMat) =
          (((-wittHestenesMat * sectorwiseCayleyMat) *
            (sectorwiseCayleyMat * wittHestenesMat)) *
            longitudinalProjectorMat) := by rw [← mul_assoc]
      _ = longitudinalProjectorMat := by
        rw [show (-wittHestenesMat * sectorwiseCayleyMat) *
            (sectorwiseCayleyMat * wittHestenesMat) = 1 by
          calc
            _ = -(wittHestenesMat *
              (sectorwiseCayleyMat * sectorwiseCayleyMat) *
              wittHestenesMat) := by noncomm_ring
            _ = 1 := by simp [hC, hK]]
        simp
  apply hL
  calc
    longitudinalProjectorMat = 1 * longitudinalProjectorMat := by simp
    _ = (-wittHestenesMat * sectorwiseCayleyMat) *
        ((sectorwiseCayleyMat * wittHestenesMat) *
          longitudinalProjectorMat) := by simpa using hleft.symm
    _ = 0 := by rw [hzero, mul_zero]

/-! Algebraic parameterized flows. -/

def longitudinalBoost (t : ℝ) : Mat8 :=
  transverseProjectorMat + Real.cosh t • longitudinalProjectorMat +
    Real.sinh t • longitudinalBoostGeneratorMat

def transversePhase (θ : ℝ) : Mat8 :=
  longitudinalProjectorMat + Real.cos θ • transverseProjectorMat +
    Real.sin θ • transverseHestenesMat

@[simp] theorem longitudinalBoost_zero : longitudinalBoost 0 = 1 := by
  rw [longitudinalBoost, Real.cosh_zero, Real.sinh_zero]
  simp [longitudinal_transverse_projectors_complete, add_comm]

@[simp] theorem transversePhase_zero : transversePhase 0 = 1 := by
  rw [transversePhase, Real.cos_zero, Real.sin_zero]
  simp [longitudinal_transverse_projectors_complete, add_comm]

end InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge
