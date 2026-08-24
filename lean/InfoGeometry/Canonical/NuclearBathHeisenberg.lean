import InfoGeometry.Canonical.NuclearBathCommutant

noncomputable section

namespace InfoGeometry.Canonical.NuclearBathHeisenberg

open InfoGeometry.Canonical.SL2SpinorLadder
open InfoGeometry.Canonical.NuclearBathCommutant
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

abbrev Alg := InfoGeometry.Canonical.SL2SpinorLadder.Alg
def grading : FiveGrading Alg :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.spinorFiveGrading

structure ThermalQuasiparticleModel where
  bath : Set Alg
  H_bath : Alg
  H_qp : Alg
  H_int : Alg
  coupling : ℝ
  H_bath_mem : H_bath ∈ bath
  H_bath_grade : H_bath ∈ grading.gZero
  H_qp_grade : H_qp ∈ grading.gZero

structure QuasiparticleCreation (M : ThermalQuasiparticleModel) where
  Q : Alg
  commutes_with_bath : CommutesWithBath M.bath Q
  creation_grade : Q ∈ grading.gPosOne

def totalHamiltonian (M : ThermalQuasiparticleModel) : Alg :=
  M.H_qp + M.H_bath + M.coupling • M.H_int

theorem bath_bracket_zero
    (M : ThermalQuasiparticleModel)
    (Q : QuasiparticleCreation M) :
    ⁅M.H_bath, Q.Q⁆ = 0 := by
  have h : ⁅Q.Q, M.H_bath⁆ = 0 :=
    Q.commutes_with_bath M.H_bath_mem
  calc
    ⁅M.H_bath, Q.Q⁆ = -⁅Q.Q, M.H_bath⁆ := by rw [lie_skew]
    _ = 0 := by rw [h, neg_zero]

theorem heisenberg_equation
    (M : ThermalQuasiparticleModel)
    (Q : QuasiparticleCreation M) :
    ⁅totalHamiltonian M, Q.Q⁆ =
      ⁅M.H_qp, Q.Q⁆ + M.coupling • ⁅M.H_int, Q.Q⁆ := by
  unfold totalHamiltonian
  rw [add_lie, add_lie, bath_bracket_zero M Q, add_zero, smul_lie]

theorem interaction_grade_split
    (Hminus Hplus Q : Alg)
    (hminus : Hminus ∈ grading.gNegOne)
    (hplus : Hplus ∈ grading.gPosOne)
    (hQ : Q ∈ grading.gPosOne) :
    ⁅Hminus + Hplus, Q⁆ ∈
      grading.gZero ⊔ grading.gPosTwo := by
  rw [add_lie]
  exact Submodule.add_mem_sup
    (grading.negOne_posOne_mem_zero hminus hQ)
    (grading.posOne_posOne_mem_posTwo hplus hQ)

theorem heisenberg_interaction_grade_split
    (M : ThermalQuasiparticleModel)
    (Q : QuasiparticleCreation M)
    (Hminus Hplus : Alg)
    (h_int : M.H_int = Hminus + Hplus)
    (hminus : Hminus ∈ grading.gNegOne)
    (hplus : Hplus ∈ grading.gPosOne) :
    ⁅totalHamiltonian M, Q.Q⁆ =
        ⁅M.H_qp, Q.Q⁆ + M.coupling • ⁅Hminus + Hplus, Q.Q⁆ ∧
      ⁅Hminus + Hplus, Q.Q⁆ ∈
        grading.gZero ⊔ grading.gPosTwo := by
  constructor
  · rw [heisenberg_equation M Q, h_int]
  · exact interaction_grade_split Hminus Hplus Q.Q
      hminus hplus Q.creation_grade

end InfoGeometry.Canonical.NuclearBathHeisenberg
