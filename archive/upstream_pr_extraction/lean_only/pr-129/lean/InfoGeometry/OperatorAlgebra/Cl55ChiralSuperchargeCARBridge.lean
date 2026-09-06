import InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge

/-!
# Cross-mode CAR readout for the Cl(5,5) chiral block calculus

This owner extends the auxiliary `2 x 2` chiral block construction with the
cross-mode identities supplied by the native `Cl(5,5)` CAR generators.  The
square-zero statements below are consequences of block placement; they are
not claims that the Clifford generators themselves are nilpotent.  No
identification of the Cuntz and Clifford carriers, and no identification of
the auxiliary block grading with native spinor chirality, is made here.
-/

namespace InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeCARBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
open InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge

theorem cl55QPlus_mul_QPlus (i j : Fin 5) :
    cl55QPlus i * cl55QPlus j = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cl55QPlus, qPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl55QMinus_mul_QMinus (i j : Fin 5) :
    cl55QMinus i * cl55QMinus j = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cl55QMinus, qMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl55QPlus_mul_QMinus (i j : Fin 5) :
    cl55QPlus i * cl55QMinus j =
      !![creation55 i * annihilation55 j, 0; 0, 0] := by
  exact qPlus_mul_qMinus _ _

theorem cl55QMinus_mul_QPlus (i j : Fin 5) :
    cl55QMinus i * cl55QPlus j =
      !![0, 0; 0, annihilation55 i * creation55 j] := by
  exact qMinus_mul_qPlus _ _

theorem cl55Q_anticomm (i j : Fin 5) :
    cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i =
      !![creation55 i * annihilation55 j, 0;
         0, annihilation55 j * creation55 i] := by
  rw [cl55QPlus_mul_QMinus, cl55QMinus_mul_QPlus]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem cl55Q_anticomm_diagonal_sum (i j : Fin 5) :
    (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 0 0 +
      (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) 1 1 =
      if i = j then (1 : Cl55) else 0 := by
  rw [cl55Q_anticomm]
  change creation55 i * annihilation55 j +
      annihilation55 j * creation55 i =
    if i = j then 1 else 0
  simpa [add_comm, eq_comm] using
    (annihilation55_creation55_anticommutator_eq j i)

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

theorem cl55Q_anticomm_gamma_commute (i j : Fin 5) :
    gamma * (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) =
      (cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i) * gamma := by
  rw [cl55Q_anticomm]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gamma]

theorem cl55Q_dirac_square_cross (i j : Fin 5) :
    (cl55QPlus i + cl55QMinus j) *
        (cl55QPlus i + cl55QMinus j) =
      cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i := by
  calc
    (cl55QPlus i + cl55QMinus j) *
        (cl55QPlus i + cl55QMinus j) =
      cl55QPlus i * cl55QPlus i +
        cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i +
        cl55QMinus j * cl55QMinus j := by noncomm_ring
    _ = cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i := by
      rw [cl55QPlus_mul_QPlus, cl55QMinus_mul_QMinus]
      simp

end InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeCARBridge
