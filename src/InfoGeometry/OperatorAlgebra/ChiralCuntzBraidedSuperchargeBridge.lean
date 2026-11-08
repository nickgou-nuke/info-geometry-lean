import InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.CelikZ3FibonacciCuntzBoundaryBridge

/-!
# Chiral Cuntz supercharges and the separate braided layer

This owner joins the verified chiral supercharge factorization to the existing
finite `Z3`/Fibonacci/Cuntz boundary bridge without identifying braid matrices
with sheet reflection.  The two layers meet only through explicit witness
data, so the existing theorem-safe boundary contracts remain intact.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralCuntzBraidedSuperchargeBridge

open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Categorical.CelikZ3FibonacciCuntzBoundaryBridge

/-! ## Generic SUSY identities -/

theorem qHamiltonian_commutes_plus {A : Type*} [Semiring A] (a b : A) :
    qAnticomm a b * qPlus a = qPlus a * qAnticomm a b := by
  rw [qAnticomm, qPlus_mul_qMinus, qMinus_mul_qPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qPlus, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem qHamiltonian_commutes_minus {A : Type*} [Semiring A] (a b : A) :
    qAnticomm a b * qMinus b = qMinus b * qAnticomm a b := by
  rw [qAnticomm, qPlus_mul_qMinus, qMinus_mul_qPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMinus, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem qSupercharge_package {A : Type*} [Ring A] (a b : A) :
    qPlus a * qPlus a = 0 ∧
    qMinus b * qMinus b = 0 ∧
    gamma * qPlus a = -(qPlus a * gamma) ∧
    gamma * qMinus b = -(qMinus b * gamma) ∧
    qAnticomm a b * qPlus a = qPlus a * qAnticomm a b ∧
    qAnticomm a b * qMinus b = qMinus b * qAnticomm a b := by
  exact ⟨qPlus_sq a, qMinus_sq b, gamma_qPlus_anticomm a,
    gamma_qMinus_anticomm b, qHamiltonian_commutes_plus a b,
    qHamiltonian_commutes_minus a b⟩

/-! ## Sheet reflection is distinct from braid reflection -/

def sheetReflection {A : Type*} [Semiring A] : Matrix Two Two A :=
  !![0, 1; 1, 0]

@[simp] theorem sheetReflection_sq {A : Type*} [Semiring A] :
    sheetReflection * sheetReflection = (1 : Matrix Two Two A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetReflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetReflection_qPlus {A : Type*} [Semiring A] (a : A) :
    sheetReflection * qPlus a * sheetReflection = qMinus a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetReflection, qPlus, qMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sheetReflection_qMinus {A : Type*} [Semiring A] (a : A) :
    sheetReflection * qMinus a * sheetReflection = qPlus a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetReflection, qPlus, qMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

/-! ## Native Cuntz supercharges -/

abbrev Cuntz3 := ChiralCuntzSUSYNative.Cuntz3

def cuntzSuperchargePlus (i : Fin 3) : Matrix Two Two Cuntz3 :=
  cuntzQPlus i

def cuntzSuperchargeMinus (i : Fin 3) : Matrix Two Two Cuntz3 :=
  cuntzQMinus i

@[simp] theorem cuntzSuperchargePlus_sq (i : Fin 3) :
    cuntzSuperchargePlus i * cuntzSuperchargePlus i = 0 :=
  cuntzQPlus_sq i

@[simp] theorem cuntzSuperchargeMinus_sq (i : Fin 3) :
    cuntzSuperchargeMinus i * cuntzSuperchargeMinus i = 0 :=
  cuntzQMinus_sq i

theorem cuntzSupercharge_dirac_square (i : Fin 3) :
    (cuntzSuperchargePlus i + cuntzSuperchargeMinus i) *
        (cuntzSuperchargePlus i + cuntzSuperchargeMinus i) =
      qAnticomm (S (R := ℝ) i) (T (R := ℝ) i) :=
  cuntzQ_dirac_square i

/-! ## Direct braided Yang--Baxter readout -/

theorem braided_yangBaxter {A : Type*} [Mul A]
    (R12 R23 : A)
    (h : HasSalihCelikZ3CartanYBE R12 R23) :
    R12 * R23 * R12 = R23 * R12 * R23 :=
  h

end InfoGeometry.OperatorAlgebra.ChiralCuntzBraidedSuperchargeBridge
