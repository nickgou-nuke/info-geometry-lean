import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearGradedBathCommutant
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra
import InfoGeometry.Physics.NuclearSolovievStateProjection

noncomputable section
namespace InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge

open Matrix
open scoped Matrix
open InfoGeometry.Physics.NuclearGradedBathCommutant
open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearPhononRPA
open InfoGeometry.Physics.NuclearSolovievStateProjection

variable {ιq ιph A : Type*} [DecidableEq ιq] [DecidableEq ιph]
  [Ring A] [Algebra ℝ A]

structure SolovievFiveGradedRealization
    (grade : ℤ → Submodule ℝ A)
    (M : ThermalQuasiparticleModel grade)
    (sys : CoupledQuasiparticlePhononSystem ιq ιph A) where
  qpMode : ιq
  phononMode : ιph
  qpModes : Finset ιq
  phononModes : Finset ιph
  qpMode_mem : qpMode ∈ qpModes
  phononMode_mem : phononMode ∈ phononModes
  qpSpectrum : ιq → ℝ
  phononSpectrum : ιph → ℝ
  qpCreation : QuasiparticleCreation grade M
  qpCreation_eq : qpCreation.op = sys.car.adag qpMode
  phononCreation_mem_bath : sys.rpa.Qdag phononMode ∈ M.bath
  H_qp_eq : M.H_qp = sys.car.freeQuasiparticleHamiltonian qpModes qpSpectrum
  H_bath_eq : M.H_bath = sys.rpa.harmonicPhononHamiltonian phononModes phononSpectrum
  rep : A →ₐ[ℝ] FullHamiltonian
  channel : TwoSpinorChannel
  represented_total_symmetric : (rep M.totalHamiltonian)ᵀ = rep M.totalHamiltonian

namespace SolovievFiveGradedRealization
variable {grade : ℤ → Submodule ℝ A} {M : ThermalQuasiparticleModel grade}
  {sys : CoupledQuasiparticlePhononSystem ιq ιph A}
variable (R : SolovievFiveGradedRealization grade M sys)

theorem qpCreation_mem_gradedBathCommutant :
    R.qpCreation.op ∈ gradedBathCommutant grade M.bath 1 :=
  R.qpCreation.mem_gradedBathCommutant

theorem car_adag_mem_bathCommutant :
    sys.car.adag R.qpMode ∈ bathCommutant M.bath := by
  rw [← R.qpCreation_eq]
  exact R.qpCreation.mem_commutant

theorem car_adag_mem_grade_one : sys.car.adag R.qpMode ∈ grade 1 := by
  rw [← R.qpCreation_eq]
  exact R.qpCreation.grade_one

theorem qpCreation_mul_phononCreation :
    R.qpCreation.op * sys.rpa.Qdag R.phononMode =
      sys.rpa.Qdag R.phononMode * R.qpCreation.op := by
  exact ((mem_bathCommutant_iff M.bath R.qpCreation.op).mp
    R.qpCreation.mem_commutant _ R.phononCreation_mem_bath).symm

theorem qpCreation_phononCreation_comm_eq_zero :
    NuclearPhononRPA.comm R.qpCreation.op (sys.rpa.Qdag R.phononMode) = 0 := by
  unfold NuclearPhononRPA.comm
  rw [R.qpCreation_mul_phononCreation, sub_self]

theorem bath_does_not_drive_bare_qp :
    ⁅M.H_bath, R.qpCreation.op⁆ = 0 :=
  bath_bracket_quasiparticle_eq_zero M R.qpCreation

end SolovievFiveGradedRealization
end InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge
