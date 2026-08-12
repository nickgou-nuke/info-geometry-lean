import Mathlib.Tactic
import InfoGeometry.Topology.AlgebraicCuntzQuotient
import InfoGeometry.Algebra.FiniteInductiveSUSY

/-!
# Native chiral supercharges over a Cuntz algebra

The two chiral sheets are represented by the ordinary matrix units in
`Matrix (Fin 2) (Fin 2) A`.  The odd supercharges are off-diagonal matrices;
their nilpotency is matrix-theoretic, while their even anticommutator is the
diagonal partner-Hamiltonian factorization.  The Cuntz specialization uses
the repository's native `S`/`T` generators and their defining relations.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

open InfoGeometry.Topology.AlgebraicCuntzQuotient

abbrev Two := Fin 2

/-! ## Generic chiral matrix units -/

/-- Positive-chirality odd channel with Weyl factor `a`. -/
def qPlus {A : Type*} [Semiring A] (a : A) : Matrix Two Two A :=
  !![0, a; 0, 0]

/-- Negative-chirality odd channel with partner factor `b`. -/
def qMinus {A : Type*} [Semiring A] (b : A) : Matrix Two Two A :=
  !![0, 0; b, 0]

/-- The even anticommutator of the two chiral odd channels. -/
def qAnticomm {A : Type*} [Semiring A] (a b : A) : Matrix Two Two A :=
  qPlus a * qMinus b + qMinus b * qPlus a

@[simp] theorem qPlus_sq {A : Type*} [Semiring A] (a : A) :
    qPlus a * qPlus a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem qMinus_sq {A : Type*} [Semiring A] (b : A) :
    qMinus b * qMinus b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem qPlus_mul_qMinus {A : Type*} [Semiring A] (a b : A) :
    qPlus a * qMinus b = !![a * b, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qPlus, qMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem qMinus_mul_qPlus {A : Type*} [Semiring A] (a b : A) :
    qMinus b * qPlus a = !![0, 0; 0, b * a] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qPlus, qMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem qAnticomm_eq_partnerHamiltonian {A : Type*} [Semiring A] (a b : A) :
    qAnticomm a b = !![a * b, 0; 0, b * a] := by
  rw [qAnticomm, qPlus_mul_qMinus, qMinus_mul_qPlus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem qDirac_square {A : Type*} [Semiring A] (a b : A) :
    (qPlus a + qMinus b) * (qPlus a + qMinus b) =
      qAnticomm a b := by
  calc
    (qPlus a + qMinus b) * (qPlus a + qMinus b) =
        qPlus a * qPlus a + qPlus a * qMinus b +
          qMinus b * qPlus a + qMinus b * qMinus b := by
      noncomm_ring
    _ = qAnticomm a b := by
      rw [qPlus_sq, qMinus_sq]
      simp [qAnticomm, add_assoc]

/-! ## Chiral grading and projectors -/

def gamma {A : Type*} [Ring A] : Matrix Two Two A :=
  !![1, 0; 0, -1]

def uPlus {A : Type*} [Ring A] : Matrix Two Two A :=
  !![1, 0; 0, 0]

def uMinus {A : Type*} [Ring A] : Matrix Two Two A :=
  !![0, 0; 0, 1]

@[simp] theorem gamma_sq {A : Type*} [Ring A] :
    gamma * gamma = (1 : Matrix Two Two A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, Matrix.mul_apply, Fin.sum_univ_two]

theorem gamma_qPlus_anticomm {A : Type*} [Ring A] (a : A) :
    gamma * qPlus a = -(qPlus a * gamma) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, qPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem gamma_qMinus_anticomm {A : Type*} [Ring A] (b : A) :
    gamma * qMinus b = -(qMinus b * gamma) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, qMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem projectors_sum {A : Type*} [Ring A] :
    uPlus + uMinus = (1 : Matrix Two Two A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uPlus, uMinus]

/-! ## Native Cuntz specialization -/

abbrev Cuntz3 := CuntzAlg ℝ (Fin 3)

def cuntzQPlus (i : Fin 3) : Matrix Two Two Cuntz3 :=
  qPlus (S (R := ℝ) i)

def cuntzQMinus (i : Fin 3) : Matrix Two Two Cuntz3 :=
  qMinus (T (R := ℝ) i)

@[simp] theorem cuntzQPlus_sq (i : Fin 3) :
    cuntzQPlus i * cuntzQPlus i = 0 :=
  qPlus_sq (S (R := ℝ) i)

@[simp] theorem cuntzQMinus_sq (i : Fin 3) :
    cuntzQMinus i * cuntzQMinus i = 0 :=
  qMinus_sq (T (R := ℝ) i)

theorem cuntzQ_anticomm (i j : Fin 3) :
    qAnticomm (S (R := ℝ) i) (T (R := ℝ) j) =
      !![S (R := ℝ) i * T (R := ℝ) j, 0;
         0, T (R := ℝ) j * S (R := ℝ) i] :=
  qAnticomm_eq_partnerHamiltonian _ _

theorem cuntzQ_anticomm_same (i : Fin 3) :
    qAnticomm (S (R := ℝ) i) (T (R := ℝ) i) =
      !![S (R := ℝ) i * T (R := ℝ) i, 0;
         0, 1] := by
  rw [cuntzQ_anticomm]
  simp [T_mul_S]

theorem cuntzQ_dirac_square (i : Fin 3) :
    (cuntzQPlus i + cuntzQMinus i) *
        (cuntzQPlus i + cuntzQMinus i) =
      qAnticomm (S (R := ℝ) i) (T (R := ℝ) i) := by
  exact qDirac_square _ _

end InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
