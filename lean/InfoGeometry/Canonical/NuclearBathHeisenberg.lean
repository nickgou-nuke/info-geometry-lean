import InfoGeometry.Canonical.NuclearBathCommutant

noncomputable section

namespace InfoGeometry.Canonical.NuclearBathHeisenberg

open InfoGeometry.Canonical.SL2SpinorLadder
open InfoGeometry.Canonical.NuclearBathCommutant
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

def grading : FiveGrading InfoGeometry.Canonical.SL2SpinorLadder.Alg :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.spinorFiveGrading

structure ThermalQuasiparticleModel where
  bath : Set InfoGeometry.Canonical.SL2SpinorLadder.Alg
  H_bath : InfoGeometry.Canonical.SL2SpinorLadder.Alg
  H_qp : InfoGeometry.Canonical.SL2SpinorLadder.Alg
  H_int : InfoGeometry.Canonical.SL2SpinorLadder.Alg
  coupling : ℝ
  H_bath_mem : H_bath ∈ bath
  H_bath_grade : H_bath ∈ grading.gZero
  H_qp_grade : H_qp ∈ grading.gZero

structure QuasiparticleCreation (M : ThermalQuasiparticleModel) where
  Q : InfoGeometry.Canonical.SL2SpinorLadder.Alg
  commutes_with_bath : CommutesWithBath M.bath Q
  creation_grade : Q ∈ grading.gPosOne

def totalHamiltonian (M : ThermalQuasiparticleModel) :
    InfoGeometry.Canonical.SL2SpinorLadder.Alg :=
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

theorem quasiparticle_term_grade
    (M : ThermalQuasiparticleModel)
    (Q : QuasiparticleCreation M) :
    ⁅M.H_qp, Q.Q⁆ ∈ grading.gPosOne :=
  SL2SpinorLadder.Alg.zero_posOne_mem_posOne M.H_qp Q.Q
    M.H_qp_grade Q.creation_grade

theorem interaction_grade_split
    (Hminus Hplus Q : InfoGeometry.Canonical.SL2SpinorLadder.Alg)
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
    (Hminus Hplus : InfoGeometry.Canonical.SL2SpinorLadder.Alg)
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

theorem interaction_grade_split_commutant
    (M : ThermalQuasiparticleModel)
    (Q : QuasiparticleCreation M)
    (Hminus Hplus : InfoGeometry.Canonical.SL2SpinorLadder.Alg)
    (hminus : Hminus ∈ grading.gNegOne)
    (hplus : Hplus ∈ grading.gPosOne)
    (hminus_comm : CommutesWithBath M.bath Hminus)
    (hplus_comm : CommutesWithBath M.bath Hplus) :
    ⁅Hminus + Hplus, Q.Q⁆ ∈ grading.gZero ⊔ grading.gPosTwo ∧
      CommutesWithBath M.bath ⁅Hminus + Hplus, Q.Q⁆ := by
  constructor
  · exact interaction_grade_split Hminus Hplus Q.Q
      hminus hplus Q.creation_grade
  · exact commutesWithBath_bracket M.bath
      (Hminus + Hplus) Q.Q
      (commutesWithBath_add M.bath Hminus Hplus
        hminus_comm hplus_comm)
      Q.commutes_with_bath

end InfoGeometry.Canonical.NuclearBathHeisenberg
