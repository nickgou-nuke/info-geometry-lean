/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Clifford.Cl55WittCircularAxes
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- Matrix units witness noncommutativity of the native Cl(5,5) chiral carrier. -/
def cl55ChiralE01 : Cl55ChiralMatrix :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def cl55ChiralE10 : Cl55ChiralMatrix :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem cl55ChiralMatrix_noncommutative_witness :
    cl55ChiralE01 * cl55ChiralE10 ≠ cl55ChiralE10 * cl55ChiralE01 := by
  intro h
  have h00 := congrArg (fun M : Cl55ChiralMatrix => M 0 0) h
  have hOne : (1 : Cl55) = 0 := by
    simpa [cl55ChiralE01, cl55ChiralE10, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero hOne

/-! The two real Clifford axes are the starting operator generators for this
bridge. Their half-sum and half-difference recover the isotropic CAR modes. -/

def cl55MajoranaPlusAxis (i : Fin 5) : Cl55 := ι55 (e_pos i)

def cl55MajoranaMinusAxis (i : Fin 5) : Cl55 := -(ι55 (f_neg i))

theorem cl55MajoranaPlusAxis_eq_hyperbolic (i : Fin 5) :
    cl55MajoranaPlusAxis i = hyperbolicAxis55 i := by
  simp [cl55MajoranaPlusAxis, hyperbolicAxis55, creation55,
    annihilation55, nbar_pair, n_pair]
  module

theorem cl55MajoranaMinusAxis_eq_elliptic (i : Fin 5) :
    cl55MajoranaMinusAxis i = ellipticAxis55 i := by
  simp [cl55MajoranaMinusAxis, ellipticAxis55, creation55,
    annihilation55, nbar_pair, n_pair]
  module

def cl55NullPlusFromMajorana (i : Fin 5) : Cl55 :=
  ((2 : ℝ)⁻¹) • (cl55MajoranaPlusAxis i + cl55MajoranaMinusAxis i)

def cl55NullMinusFromMajorana (i : Fin 5) : Cl55 :=
  ((2 : ℝ)⁻¹) • (cl55MajoranaPlusAxis i - cl55MajoranaMinusAxis i)

@[simp] theorem cl55NullPlusFromMajorana_eq_creation (i : Fin 5) :
    cl55NullPlusFromMajorana i = creation55 i := by
  change ((2 : ℝ)⁻¹) •
    (cl55MajoranaPlusAxis i + cl55MajoranaMinusAxis i) = creation55 i
  rw [cl55MajoranaPlusAxis_eq_hyperbolic,
    cl55MajoranaMinusAxis_eq_elliptic]
  simp [hyperbolicAxis55, ellipticAxis55]
  module

@[simp] theorem cl55NullMinusFromMajorana_eq_annihilation (i : Fin 5) :
    cl55NullMinusFromMajorana i = annihilation55 i := by
  change ((2 : ℝ)⁻¹) •
    (cl55MajoranaPlusAxis i - cl55MajoranaMinusAxis i) = annihilation55 i
  rw [cl55MajoranaPlusAxis_eq_hyperbolic,
    cl55MajoranaMinusAxis_eq_elliptic]
  simp [hyperbolicAxis55, ellipticAxis55]
  module

def cl55QPlus (i : Fin 5) : Cl55ChiralMatrix :=
  qPlus (cl55NullPlusFromMajorana i)

def cl55QMinus (i : Fin 5) : Cl55ChiralMatrix :=
  qMinus (cl55NullMinusFromMajorana i)

@[simp] theorem cl55QPlus_sq (i : Fin 5) :
    cl55QPlus i * cl55QPlus i = 0 := by
  change qPlus (cl55NullPlusFromMajorana i) *
    qPlus (cl55NullPlusFromMajorana i) = 0
  rw [cl55NullPlusFromMajorana_eq_creation]
  exact qPlus_sq _

@[simp] theorem cl55QMinus_sq (i : Fin 5) :
    cl55QMinus i * cl55QMinus i = 0 := by
  change qMinus (cl55NullMinusFromMajorana i) *
    qMinus (cl55NullMinusFromMajorana i) = 0
  rw [cl55NullMinusFromMajorana_eq_annihilation]
  exact qMinus_sq _

theorem cl55QPlus_mul_QPlus (i j : Fin 5) :
    cl55QPlus i * cl55QPlus j = 0 := by
  exact qPlus_mul_qPlus _ _

theorem cl55QMinus_mul_QMinus (i j : Fin 5) :
    cl55QMinus i * cl55QMinus j = 0 := by
  exact qMinus_mul_qMinus _ _

theorem cl55QPlus_mul_QMinus (i : Fin 5) :
    cl55QPlus i * cl55QMinus i =
      !![creation55 i * annihilation55 i, 0; 0, 0] := by
  simpa [cl55QPlus, cl55QMinus] using
    qPlus_mul_qMinus (creation55 i) (annihilation55 i)

theorem cl55QMinus_mul_QPlus (i : Fin 5) :
    cl55QMinus i * cl55QPlus i =
      !![0, 0; 0, annihilation55 i * creation55 i] := by
  simpa [cl55QPlus, cl55QMinus] using
    qMinus_mul_qPlus (creation55 i) (annihilation55 i)

theorem cl55Q_anticomm_same (i : Fin 5) :
    cl55QPlus i * cl55QMinus i +
        cl55QMinus i * cl55QPlus i =
      !![creation55 i * annihilation55 i, 0;
         0, annihilation55 i * creation55 i] := by
  simpa [cl55QPlus, cl55QMinus, qAnticomm] using
    qAnticomm_eq_partnerHamiltonian (creation55 i) (annihilation55 i)

theorem cl55Q_anticomm (i j : Fin 5) :
    cl55QPlus i * cl55QMinus j +
        cl55QMinus j * cl55QPlus i =
      !![creation55 i * annihilation55 j, 0;
         0, annihilation55 j * creation55 i] := by
  simpa [cl55QPlus, cl55QMinus, qAnticomm] using
    qAnticomm_eq_partnerHamiltonian (creation55 i) (annihilation55 j)

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
