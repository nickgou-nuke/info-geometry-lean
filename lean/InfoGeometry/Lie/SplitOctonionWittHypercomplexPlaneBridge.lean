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

set_option maxHeartbeats 800000

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

def wittHestenesMat : Mat8 :=
  exchangeInvolutionMat * peirceGradingMat

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

@[simp] theorem longitudinalTransverseMat_sq :
    longitudinalTransverseMat * longitudinalTransverseMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, longitudinalTransverseMat, Fin.sum_univ_eight]

theorem longitudinalTransverseMat_comm_peirce :
    longitudinalTransverseMat * peirceGradingMat =
      peirceGradingMat * longitudinalTransverseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, longitudinalTransverseMat,
      peirceGradingMat, Fin.sum_univ_eight]

theorem longitudinalTransverseMat_comm_exchange :
    longitudinalTransverseMat * exchangeInvolutionMat =
      exchangeInvolutionMat * longitudinalTransverseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, longitudinalTransverseMat,
      exchangeInvolutionMat, Fin.sum_univ_eight]

@[simp] theorem wittHestenesMat_sq :
    wittHestenesMat * wittHestenesMat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittHestenesMat, Matrix.mul_apply,
      peirceGradingMat, exchangeInvolutionMat, Fin.sum_univ_eight]

theorem longitudinalTransverseMat_comm_wittHestenes :
    longitudinalTransverseMat * wittHestenesMat =
      wittHestenesMat * longitudinalTransverseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittHestenesMat, Matrix.mul_apply,
      longitudinalTransverseMat, peirceGradingMat,
      exchangeInvolutionMat, Fin.sum_univ_eight]

@[simp] theorem longitudinalProjectorMat_sq :
    longitudinalProjectorMat * longitudinalProjectorMat =
      longitudinalProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, Matrix.mul_apply,
      Fin.sum_univ_eight]

@[simp] theorem transverseProjectorMat_sq :
    transverseProjectorMat * transverseProjectorMat =
      transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseProjectorMat, Matrix.mul_apply,
      Fin.sum_univ_eight]

theorem longitudinal_transverse_projectors_orthogonal :
    longitudinalProjectorMat * transverseProjectorMat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat,
      Matrix.mul_apply, longitudinalTransverseMat, Fin.sum_univ_eight]

theorem transverse_longitudinal_projectors_orthogonal :
    transverseProjectorMat * longitudinalProjectorMat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat,
      Matrix.mul_apply, longitudinalTransverseMat, Fin.sum_univ_eight]

theorem longitudinal_transverse_projectors_complete :
    longitudinalProjectorMat + transverseProjectorMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, transverseProjectorMat,
      Matrix.add_apply, Matrix.one_apply] <;> norm_num

theorem exchange_comm_longitudinalProjectorMat :
    exchangeInvolutionMat * longitudinalProjectorMat =
      longitudinalProjectorMat * exchangeInvolutionMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, Matrix.mul_apply,
      exchangeInvolutionMat, Fin.sum_univ_eight]

@[simp] theorem longitudinalBoostGeneratorMat_sq :
    longitudinalBoostGeneratorMat * longitudinalBoostGeneratorMat =
      longitudinalProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalBoostGeneratorMat, longitudinalProjectorMat,
      peirceGradingMat, Matrix.mul_apply, Fin.sum_univ_eight]

@[simp] theorem transverseHestenesMat_sq :
    transverseHestenesMat * transverseHestenesMat =
      -transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseHestenesMat, wittHestenesMat,
      transverseProjectorMat, Matrix.mul_apply,
      peirceGradingMat,
      exchangeInvolutionMat, Fin.sum_univ_eight] <;> norm_num

@[simp] theorem sectorwiseCayleyMat_sq :
    sectorwiseCayleyMat * sectorwiseCayleyMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalProjectorMat,
      transverseProjectorMat, Matrix.mul_apply,
      exchangeInvolutionMat,
      Fin.sum_univ_eight] <;> norm_num

/-! The sectorwise Cayley readout is intrinsic to the Peirce carrier.  It
commutes with the longitudinal/transverse grading, but its relation with the
intrinsic Witt Hestenes matrix is sector-dependent: it anticommutes on the
longitudinal plane and commutes on the transverse planes.  These are operator
identities on the 8D readout, not claims about ambient split-octonion
multiplication or about the separate 16D copy-doubling phase. -/

theorem sectorwiseCayleyMat_comm_longitudinalTransverse :
    sectorwiseCayleyMat * longitudinalTransverseMat =
      longitudinalTransverseMat * sectorwiseCayleyMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalTransverseMat,
      longitudinalProjectorMat, transverseProjectorMat,
      exchangeInvolutionMat, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

theorem sectorwiseCayleyMat_longitudinal_wittHestenes_anticommute :
    (sectorwiseCayleyMat * wittHestenesMat) * longitudinalProjectorMat =
      -((wittHestenesMat * sectorwiseCayleyMat) *
        longitudinalProjectorMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, wittHestenesMat,
      longitudinalProjectorMat, transverseProjectorMat,
      longitudinalTransverseMat, exchangeInvolutionMat,
      peirceGradingMat, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

theorem sectorwiseCayleyMat_transverse_wittHestenes_commute :
    (sectorwiseCayleyMat * wittHestenesMat) * transverseProjectorMat =
      (wittHestenesMat * sectorwiseCayleyMat) *
        transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, wittHestenesMat,
      longitudinalProjectorMat, transverseProjectorMat,
      longitudinalTransverseMat, exchangeInvolutionMat,
      peirceGradingMat, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

/-- The global Cayley/Hestenes relation records the opposite signs on the
longitudinal and transverse sectors.  It is the honest replacement for a
false global commutation claim: conjugating the finite Hestenes matrix by the
sectorwise Cayley readout produces the middle-sign twist. -/
theorem sectorwiseCayleyMat_wittHestenes_sector_twist :
    sectorwiseCayleyMat * wittHestenesMat * sectorwiseCayleyMat =
      -(longitudinalTransverseMat * wittHestenesMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, wittHestenesMat,
      longitudinalTransverseMat, longitudinalProjectorMat,
      transverseProjectorMat, exchangeInvolutionMat,
      peirceGradingMat, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

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

/-! The square of the combined Cayley--Hestenes operator is the grading
involution.  This is a formal consequence of the already proved sector twist
and `wittHestenesMat_sq`; it does not identify the grading with a
Frobenius--Schur indicator or with an anti-linear real structure. -/
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
      simp

theorem longitudinalProjectorMat_eq_half_add_grading :
    longitudinalProjectorMat =
      (1 / 2 : ℝ) • (1 + longitudinalTransverseMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longitudinalProjectorMat, longitudinalTransverseMat,
      Matrix.add_apply, Matrix.one_apply] <;> norm_num

theorem transverseProjectorMat_eq_half_sub_grading :
    transverseProjectorMat =
      (1 / 2 : ℝ) • (1 - longitudinalTransverseMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseProjectorMat, longitudinalTransverseMat,
      Matrix.sub_apply, Matrix.one_apply] <;> norm_num

theorem cayley_hestenes_commutator_localized :
    sectorwiseCayleyMat * wittHestenesMat -
        wittHestenesMat * sectorwiseCayleyMat =
      (2 : ℝ) • (longitudinalProjectorMat * peirceGradingMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, wittHestenesMat,
      longitudinalProjectorMat, transverseProjectorMat,
      longitudinalTransverseMat, exchangeInvolutionMat,
      peirceGradingMat, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_eight] <;>
    norm_num

theorem cayley_hestenes_anticommutator_localized :
    sectorwiseCayleyMat * wittHestenesMat +
        wittHestenesMat * sectorwiseCayleyMat =
      (-2 : ℝ) • (transverseProjectorMat * wittHestenesMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, wittHestenesMat,
      longitudinalProjectorMat, transverseProjectorMat,
      longitudinalTransverseMat, exchangeInvolutionMat,
      peirceGradingMat, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_eight] <;>
    norm_num

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

theorem sectorwiseCayleyMat_on_longitudinal :
    sectorwiseCayleyMat * longitudinalProjectorMat =
      exchangeInvolutionMat * longitudinalProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalProjectorMat,
      transverseProjectorMat, exchangeInvolutionMat,
      Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

theorem sectorwiseCayleyMat_on_transverse :
    sectorwiseCayleyMat * transverseProjectorMat =
      -transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalProjectorMat,
      transverseProjectorMat, exchangeInvolutionMat,
      Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

theorem longitudinal_on_sectorwiseCayleyMat :
    longitudinalProjectorMat * sectorwiseCayleyMat =
      longitudinalProjectorMat * exchangeInvolutionMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalProjectorMat,
      transverseProjectorMat, exchangeInvolutionMat,
      Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

theorem transverse_on_sectorwiseCayleyMat :
    transverseProjectorMat * sectorwiseCayleyMat =
      -transverseProjectorMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorwiseCayleyMat, longitudinalProjectorMat,
      transverseProjectorMat, exchangeInvolutionMat,
      Matrix.mul_apply, Fin.sum_univ_eight] <;>
    norm_num

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
