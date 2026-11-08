import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

/-!
# Real Clifford carrier for signature (1,3)

This file introduces the native Mathlib Clifford algebra for the diagonal
quadratic form `(+---)` on `ℝ⁴` and records the constructive generator and
even-grade facts needed by the Hestenes bridge.
-/

noncomputable section
namespace HestenesCl14

open BigOperators

abbrev V14 := InfoGeometry.Algebra.FiniteSpin.Vec4R

 def coord4 (i : Fin 4) : V14 →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def qCoeff (i : Fin 4) : ℝ :=
  if i = 0 then 1 else -1

noncomputable def Q14 : QuadraticForm ℝ V14 :=
  ∑ i : Fin 4, qCoeff i • QuadraticMap.linMulLin (coord4 i) (coord4 i)

 def basisVec (i : Fin 4) : V14 := fun j => if j = i then 1 else 0

@[simp] theorem Q14_apply (x : V14) :
    Q14 x = ∑ i : Fin 4, qCoeff i * x i ^ 2 := by
  classical
  simp [Q14, qCoeff, QuadraticMap.linMulLin, coord4, Fin.sum_univ_succ]
  ring

@[simp] theorem qCoeff_zero : qCoeff 0 = 1 := by simp [qCoeff]

@[simp] theorem qCoeff_one : qCoeff 1 = -1 := by simp [qCoeff]

@[simp] theorem qCoeff_two : qCoeff 2 = -1 := by simp [qCoeff]

@[simp] theorem qCoeff_three : qCoeff 3 = -1 := by simp [qCoeff]

@[simp] theorem Q14_basis_zero : Q14 (basisVec 0) = 1 := by
  simp [Q14_apply, basisVec, qCoeff]

@[simp] theorem Q14_basis_one : Q14 (basisVec 1) = -1 := by
  simp [Q14_apply, basisVec, qCoeff]

@[simp] theorem Q14_basis_two : Q14 (basisVec 2) = -1 := by
  simp [Q14_apply, basisVec, qCoeff]

@[simp] theorem Q14_basis_three : Q14 (basisVec 3) = -1 := by
  simp [Q14_apply, basisVec, qCoeff]

theorem Q14_basis (i : Fin 4) : Q14 (basisVec i) = qCoeff i := by
  fin_cases i <;>
    simp [Q14_apply, basisVec, qCoeff, Fin.sum_univ_succ] <;> ring

abbrev Cl14 := CliffordAlgebra Q14
abbrev ClPlus14 := CliffordAlgebra.even Q14
abbrev ι14 : V14 →ₗ[ℝ] Cl14 := CliffordAlgebra.ι Q14

 def gamma (i : Fin 4) : Cl14 := ι14 (basisVec i)

@[simp] theorem gamma_sq (i : Fin 4) :
    gamma i * gamma i = algebraMap ℝ Cl14 (qCoeff i) := by
  rw [gamma, CliffordAlgebra.ι_sq_scalar]
  rw [Q14_basis]

@[simp] theorem gamma_zero_sq : gamma 0 * gamma 0 = 1 := by
  rw [gamma_sq, qCoeff_zero]
  simp

@[simp] theorem gamma_one_sq : gamma 1 * gamma 1 = -1 := by
  rw [gamma_sq, qCoeff_one]
  simp

@[simp] theorem gamma_two_sq : gamma 2 * gamma 2 = -1 := by
  rw [gamma_sq, qCoeff_two]
  simp

@[simp] theorem gamma_three_sq : gamma 3 * gamma 3 = -1 := by
  rw [gamma_sq, qCoeff_three]
  simp

@[simp] theorem basis_isOrtho {i j : Fin 4} (hij : i ≠ j) :
    Q14.IsOrtho (basisVec i) (basisVec j) := by
  classical
  fin_cases i <;> fin_cases j <;>
    simp_all [QuadraticMap.isOrtho_def, Q14_apply, basisVec, qCoeff,
      Fin.sum_univ_succ]

theorem gamma_anticomm {i j : Fin 4} (hij : i ≠ j) :
    gamma i * gamma j + gamma j * gamma i = 0 := by
  have h := CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    (Q := Q14) (basis_isOrtho hij)
  rw [gamma, gamma, h]
  exact neg_add_cancel _

@[simp] theorem gamma_zero_mem_odd :
    gamma 0 ∈ CliffordAlgebra.evenOdd Q14 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one Q14 (basisVec 0)

@[simp] theorem gamma_one_mem_odd :
    gamma 1 ∈ CliffordAlgebra.evenOdd Q14 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one Q14 (basisVec 1)

@[simp] theorem gamma_two_mem_odd :
    gamma 2 ∈ CliffordAlgebra.evenOdd Q14 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one Q14 (basisVec 2)

@[simp] theorem gamma_three_mem_odd :
    gamma 3 ∈ CliffordAlgebra.evenOdd Q14 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one Q14 (basisVec 3)

 def sigma (k : Fin 3) : Cl14 :=
  match k with
  | 0 => gamma 1 * gamma 0
  | 1 => gamma 2 * gamma 0
  | 2 => gamma 3 * gamma 0

  def sigmaEven (k : Fin 3) : ClPlus14 :=
   match k with
   | 0 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 1) (basisVec 0)
   | 1 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 2) (basisVec 0)
   | 2 => (CliffordAlgebra.even.ι Q14).bilin (basisVec 3) (basisVec 0)

  @[simp] theorem sigmaEven_zero_val :
     (sigmaEven 0 : Cl14) = sigma 0 := by rfl

  @[simp] theorem sigmaEven_one_val :
     (sigmaEven 1 : Cl14) = sigma 1 := by rfl

  @[simp] theorem sigmaEven_two_val :
     (sigmaEven 2 : Cl14) = sigma 2 := by rfl

@[simp] theorem sigmaEven_zero_sq : sigmaEven 0 * sigmaEven 0 = 1 := by
  apply Subtype.ext
  change (gamma 1 * gamma 0) * (gamma 1 * gamma 0) = (1 : Cl14)
  have h : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) := by
    exact eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  calc
    (gamma 1 * gamma 0) * (gamma 1 * gamma 0) =
        gamma 1 * (gamma 0 * gamma 1) * gamma 0 := by
          simp only [mul_assoc]
    _ = gamma 1 * (-(gamma 1 * gamma 0)) * gamma 0 := by rw [h]
    _ = 1 := by
      simp only [neg_mul, mul_neg, mul_assoc]
      rw [← mul_assoc, gamma_one_sq, gamma_zero_sq]
      norm_num

  end HestenesCl14
end noncomputable section
