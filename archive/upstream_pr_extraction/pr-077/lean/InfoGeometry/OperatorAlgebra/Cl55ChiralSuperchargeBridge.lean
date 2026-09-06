import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

/-!
# Native `Cl(5,5)` chiral supercharge bridge

This owner reuses the generic off-diagonal chiral matrix construction from
`ChiralCuntzSUSYNative` with the native `Cl(5,5)` CAR generators.  It does not
identify the Cuntz and Clifford carriers; it only records the common matrix
calculus and the grade routing of the Clifford diagonal factors.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

abbrev Cl55ChiralMatrix := Matrix (Fin 2) (Fin 2) Cl55

def cl55QPlus (i : Fin 5) : Cl55ChiralMatrix :=
  qPlus (creation55 i)

def cl55QMinus (i : Fin 5) : Cl55ChiralMatrix :=
  qMinus (annihilation55 i)

@[simp] theorem cl55QPlus_sq (i : Fin 5) :
    cl55QPlus i * cl55QPlus i = 0 := by
  exact qPlus_sq (creation55 i)

@[simp] theorem cl55QMinus_sq (i : Fin 5) :
    cl55QMinus i * cl55QMinus i = 0 := by
  exact qMinus_sq (annihilation55 i)

theorem cl55QPlus_mul_QPlus (i j : Fin 5) :
    cl55QPlus i * cl55QPlus j = 0 := by
  exact qPlus_mul_qPlus _ _

theorem cl55QMinus_mul_QMinus (i j : Fin 5) :
    cl55QMinus i * cl55QMinus j = 0 := by
  exact qMinus_mul_qMinus _ _

theorem cl55QPlus_mul_QMinus (i : Fin 5) :
    cl55QPlus i * cl55QMinus i =
      !![creation55 i * annihilation55 i, 0; 0, 0] := by
  exact qPlus_mul_qMinus _ _

theorem cl55QMinus_mul_QPlus (i : Fin 5) :
    cl55QMinus i * cl55QPlus i =
      !![0, 0; 0, annihilation55 i * creation55 i] := by
  exact qMinus_mul_qPlus _ _

theorem cl55Q_anticomm_same (i : Fin 5) :
    cl55QPlus i * cl55QMinus i +
        cl55QMinus i * cl55QPlus i =
      !![creation55 i * annihilation55 i, 0;
         0, annihilation55 i * creation55 i] := by
  exact qAnticomm_eq_partnerHamiltonian _ _

theorem cl55Q_anticomm (i j : Fin 5) :
    cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i =
      !![creation55 i * annihilation55 j, 0;
         0, annihilation55 j * creation55 i] := by
  exact qAnticomm_eq_partnerHamiltonian _ _

theorem cl55Q_dirac_square (i : Fin 5) :
    (cl55QPlus i + cl55QMinus i) *
        (cl55QPlus i + cl55QMinus i) =
      cl55QPlus i * cl55QMinus i +
        cl55QMinus i * cl55QPlus i := by
  exact qDirac_square _ _

theorem cl55Gamma_QPlus_anticomm (i : Fin 5) :
    gamma * cl55QPlus i = -(cl55QPlus i * gamma) := by
  exact gamma_qPlus_anticomm _

theorem cl55Gamma_QMinus_anticomm (i : Fin 5) :
    gamma * cl55QMinus i = -(cl55QMinus i * gamma) := by
  exact gamma_qMinus_anticomm _

theorem cl55Gamma_commutator_QPlus (i : Fin 5) :
    gamma * cl55QPlus i - cl55QPlus i * gamma =
      cl55QPlus i + cl55QPlus i := by
  exact gamma_commutator_qPlus _

theorem cl55Gamma_commutator_QMinus (i : Fin 5) :
    gamma * cl55QMinus i - cl55QMinus i * gamma =
      -(cl55QMinus i + cl55QMinus i) := by
  exact gamma_commutator_qMinus _

theorem cl55Q_anticomm_same_left_entry_mem_grade_zero (i : Fin 5) :
    (cl55QPlus i * cl55QMinus i +
        cl55QMinus i * cl55QPlus i) 0 0 ∈
      cl55GradeSubmodule 0 := by
  rw [cl55Q_anticomm_same]
  simpa using creation55_mul_annihilation55_mem_grade_zero i i

theorem cl55Q_anticomm_same_right_entry_mem_grade_zero (i : Fin 5) :
    (cl55QPlus i * cl55QMinus i +
        cl55QMinus i * cl55QPlus i) 1 1 ∈
      cl55GradeSubmodule 0 := by
  rw [cl55Q_anticomm_same]
  simpa using annihilation55_mul_creation55_mem_grade_zero i i

theorem cl55Q_anticomm_left_entry_mem_grade_zero (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 0 0 ∈
      cl55GradeSubmodule 0 := by
  rw [cl55Q_anticomm]
  simpa using creation55_mul_annihilation55_mem_grade_zero i j

theorem cl55Q_anticomm_right_entry_mem_grade_zero (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 1 1 ∈
      cl55GradeSubmodule 0 := by
  rw [cl55Q_anticomm]
  simpa using annihilation55_mul_creation55_mem_grade_zero j i

theorem cl55Q_anticomm_diag_sum_readback (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 0 0 +
      (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 1 1 =
      if i = j then 1 else 0 := by
  rw [cl55Q_anticomm]
  simpa [add_comm, eq_comm] using
    (annihilation55_creation55_anticommutator_eq j i)

theorem cl55Q_anticomm_comm_QPlus (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) * cl55QPlus i -
      cl55QPlus i *
        (cl55QPlus i * cl55QMinus j +
          cl55QMinus j * cl55QPlus i) = 0 := by
  exact qAnticomm_comm_qPlus _ _

theorem cl55Q_anticomm_comm_QMinus (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) * cl55QMinus j -
      cl55QMinus j *
        (cl55QPlus i * cl55QMinus j +
          cl55QMinus j * cl55QPlus i) = 0 := by
  exact qAnticomm_comm_qMinus _ _

theorem cl55Gamma_commutator_Q_anticomm (i j : Fin 5) :
    gamma *
        (cl55QPlus i * cl55QMinus j +
          cl55QMinus j * cl55QPlus i) -
      (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) * gamma = 0 := by
  exact gamma_commutator_qAnticomm _ _

end InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
