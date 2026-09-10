import Mathlib
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Optics.OperatorLiftCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite chiral operator lift

This owner formalizes the finite algebraic core of the chiral/operator lift:
the split `(1,1)` sheet atom, its even/odd decomposition by conjugation, and
the two explicit nilpotent CAR matrices.  It does not assert a Lorentz-group
representation, a KMS state, or a quantum-group deformation.
-/

open scoped Matrix

namespace InfoGeometry.Optics.ChiralLorentzOperatorLift

set_option linter.unusedSimpArgs false

noncomputable section

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

open InfoGeometry.Clifford.Cl11Matrix

def parity : M2R := Eplus
def sheetFlip : M2R := J1
def splitGenerator : M2R := Eminus

theorem parity_sq : parity * parity = 1 := by
  exact Eplus_sq

theorem sheetFlip_sq : sheetFlip * sheetFlip = 1 := by
  exact J1_sq

theorem parity_mul_splitGenerator_anticomm :
    parity * splitGenerator + splitGenerator * parity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parity, splitGenerator, Eplus, Eminus, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem parity_mul_sheetFlip_anticomm :
    parity * sheetFlip + sheetFlip * parity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parity, sheetFlip, Eplus, J1, Matrix.mul_apply,
      Fin.sum_univ_two]

def evenPart (A : M2R) : M2R := A + parity * A * parity
def oddPart (A : M2R) : M2R := A - parity * A * parity

theorem evenPart_add_oddPart (A : M2R) :
    evenPart A + oddPart A = (2 : ℝ) • A := by
  simp [evenPart, oddPart, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, two_smul]

theorem parity_mul_evenPart_eq_evenPart_mul_parity (A : M2R) :
    parity * evenPart A = evenPart A * parity := by
  unfold evenPart
  calc
    parity * (A + parity * A * parity) =
        parity * A + parity * (parity * A * parity) := by
          rw [mul_add]
    _ = parity * A + A * parity := by
          congr 1
          rw [← mul_assoc parity (parity * A) parity,
            ← mul_assoc parity parity A, parity_sq, one_mul]
    _ = (A + parity * A * parity) * parity := by
          have hpp : parity * A * parity * parity = parity * A := by
            calc
              parity * A * parity * parity =
                  (parity * A) * (parity * parity) := by noncomm_ring
              _ = parity * A := by rw [parity_sq, mul_one]
          rw [add_mul, hpp, add_comm]

theorem parity_mul_oddPart_eq_neg_oddPart_mul_parity (A : M2R) :
    parity * oddPart A = -(oddPart A * parity) := by
  unfold oddPart
  calc
    parity * (A - parity * A * parity) =
        parity * A - parity * (parity * A * parity) := by
          rw [mul_sub]
    _ = parity * A - A * parity := by
          congr 1
          rw [← mul_assoc parity (parity * A) parity,
            ← mul_assoc parity parity A, parity_sq, one_mul]
    _ = -((A - parity * A * parity) * parity) := by
          have hpp : parity * A * parity * parity = parity * A := by
            calc
              parity * A * parity * parity =
                  (parity * A) * (parity * parity) := by noncomm_ring
              _ = parity * A := by rw [parity_sq, mul_one]
          rw [sub_mul, hpp, neg_sub]

def create : M2C := !![(0 : ℂ), 1; 0, 0]
def annihilate : M2C := !![(0 : ℂ), 0; 1, 0]

def anticommutator (A B : M2C) : M2C := A * B + B * A

theorem create_sq : create * create = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [create, Matrix.mul_apply, Fin.sum_univ_two]

theorem annihilate_sq : annihilate * annihilate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilate, Matrix.mul_apply, Fin.sum_univ_two]

theorem create_annihilate_anticommutator :
    anticommutator create annihilate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anticommutator, create, annihilate, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

theorem annihilate_create_anticommutator :
    anticommutator annihilate create = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anticommutator, create, annihilate, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

def adjointAction (U : M2Cˣ) (A : M2C) : M2C :=
  (U : M2C) * A * (↑(U⁻¹) : M2C)

theorem adjointAction_mul (U V : M2Cˣ) (A : M2C) :
    adjointAction (U * V) A = adjointAction U (adjointAction V A) := by
  simp [adjointAction, mul_assoc]

theorem adjointAction_one (A : M2C) : adjointAction 1 A = A := by
  simp [adjointAction]

theorem adjointAction_add (U : M2Cˣ) (A B : M2C) :
    adjointAction U (A + B) = adjointAction U A + adjointAction U B := by
  simp [adjointAction, mul_add, add_mul]

theorem adjointAction_mul_operator (U : M2Cˣ) (A B : M2C) :
    adjointAction U (A * B) =
      adjointAction U A * adjointAction U B := by
  simp [adjointAction, mul_assoc]

/-! ## Operator-valued doubled carrier -/

abbrev OperatorMatrix (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (Module.End ℂ W)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def operatorParity : OperatorMatrix W :=
  !![(1 : Module.End ℂ W), 0; 0, -1]

def operatorSheetFlip : OperatorMatrix W :=
  !![(0 : Module.End ℂ W), 1; 1, 0]

def operatorSplitGenerator : OperatorMatrix W :=
  !![(0 : Module.End ℂ W), 1; -1, 0]

theorem operatorParity_sq : operatorParity (W := W) * operatorParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorParity, Matrix.mul_apply, Fin.sum_univ_two,
      Module.End.mul_apply]

theorem operatorSheetFlip_sq :
    operatorSheetFlip (W := W) * operatorSheetFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSheetFlip, Matrix.mul_apply, Fin.sum_univ_two,
      Module.End.mul_apply]

theorem operatorParity_sheetFlip_anticomm :
    operatorParity (W := W) * operatorSheetFlip +
        operatorSheetFlip * operatorParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorParity, operatorSheetFlip, Matrix.mul_apply,
      Fin.sum_univ_two, Module.End.mul_apply]

theorem operatorParity_splitGenerator_anticomm :
    operatorParity (W := W) * operatorSplitGenerator +
        operatorSplitGenerator * operatorParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorParity, operatorSplitGenerator, Matrix.mul_apply,
      Fin.sum_univ_two, Module.End.mul_apply]

def operatorEvenPart (A : OperatorMatrix W) : OperatorMatrix W :=
  A + operatorParity * A * operatorParity

def operatorOddPart (A : OperatorMatrix W) : OperatorMatrix W :=
  A - operatorParity * A * operatorParity

theorem operatorEvenPart_add_oddPart (A : OperatorMatrix W) :
    operatorEvenPart A + operatorOddPart A = (2 : ℂ) • A := by
  simp [operatorEvenPart, operatorOddPart, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm, two_smul]

theorem operatorParity_mul_evenPart_eq_evenPart_mul_parity
    (A : OperatorMatrix W) :
    operatorParity * operatorEvenPart A =
      operatorEvenPart A * operatorParity := by
  unfold operatorEvenPart
  calc
    operatorParity * (A + operatorParity * A * operatorParity) =
        operatorParity * A + A * operatorParity := by
          rw [mul_add]
          congr 1
          rw [← mul_assoc operatorParity (operatorParity * A) operatorParity,
            ← mul_assoc operatorParity operatorParity A, operatorParity_sq,
            one_mul]
    _ = (A + operatorParity * A * operatorParity) * operatorParity := by
          have h : operatorParity * A * operatorParity * operatorParity =
              operatorParity * A := by
            simp only [Matrix.mul_assoc]
            rw [operatorParity_sq, Matrix.mul_one]
          rw [add_mul, h, add_comm]

theorem operatorParity_mul_oddPart_eq_neg_oddPart_mul_parity
    (A : OperatorMatrix W) :
    operatorParity * operatorOddPart A =
      -(operatorOddPart A * operatorParity) := by
  unfold operatorOddPart
  calc
    operatorParity * (A - operatorParity * A * operatorParity) =
        operatorParity * A - A * operatorParity := by
          rw [mul_sub]
          congr 1
          rw [← mul_assoc operatorParity (operatorParity * A) operatorParity,
            ← mul_assoc operatorParity operatorParity A, operatorParity_sq,
            one_mul]
    _ = -((A - operatorParity * A * operatorParity) * operatorParity) := by
          have h : operatorParity * A * operatorParity * operatorParity =
              operatorParity * A := by
            simp only [Matrix.mul_assoc]
            rw [operatorParity_sq, Matrix.mul_one]
          rw [sub_mul, h, neg_sub]

def operatorCommutator (A B : OperatorMatrix W) : OperatorMatrix W :=
  A * B - B * A

theorem operatorCommutator_mul (D A B : OperatorMatrix W) :
    operatorCommutator D (A * B) =
      operatorCommutator D A * B + A * operatorCommutator D B := by
  unfold operatorCommutator
  noncomm_ring

theorem operatorCommutator_commutator (D E A : OperatorMatrix W) :
    operatorCommutator D (operatorCommutator E A) -
        operatorCommutator E (operatorCommutator D A) =
      operatorCommutator (operatorCommutator D E) A := by
  unfold operatorCommutator
  noncomm_ring

def operatorAdjointAction (U : (OperatorMatrix W)ˣ)
    (A : OperatorMatrix W) : OperatorMatrix W :=
  (U : OperatorMatrix W) * A * (↑(U⁻¹) : OperatorMatrix W)

theorem operatorAdjointAction_one (A : OperatorMatrix W) :
    operatorAdjointAction (1 : (OperatorMatrix W)ˣ) A = A := by
  simp [operatorAdjointAction]

theorem operatorAdjointAction_mul (U V : (OperatorMatrix W)ˣ)
    (A : OperatorMatrix W) :
    operatorAdjointAction (U * V) A =
      operatorAdjointAction U (operatorAdjointAction V A) := by
  simp only [operatorAdjointAction, Units.val_mul, Units.val_inv]
  noncomm_ring

theorem operatorAdjointAction_add (U : (OperatorMatrix W)ˣ)
    (A B : OperatorMatrix W) :
    operatorAdjointAction U (A + B) =
      operatorAdjointAction U A + operatorAdjointAction U B := by
  simp only [operatorAdjointAction, mul_add, add_mul]

theorem operatorAdjointAction_mul_operator (U : (OperatorMatrix W)ˣ)
    (A B : OperatorMatrix W) :
    operatorAdjointAction U (A * B) =
      operatorAdjointAction U A * operatorAdjointAction U B := by
  simp only [operatorAdjointAction, ← mul_assoc]
  rw [mul_assoc ((U : OperatorMatrix W) * A)
      (↑(U⁻¹) : OperatorMatrix W) (U : OperatorMatrix W)]
  rw [show (↑(U⁻¹) : OperatorMatrix W) * (U : OperatorMatrix W) = 1
      from Units.inv_mul U]
  rw [mul_one]

def operatorCreation : OperatorMatrix W :=
  !![(0 : Module.End ℂ W), 1; 0, 0]

def operatorAnnihilation : OperatorMatrix W :=
  !![(0 : Module.End ℂ W), 0; 1, 0]

theorem operatorCreation_sq :
    operatorCreation (W := W) * operatorCreation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorCreation, Matrix.mul_apply, Fin.sum_univ_two,
      Module.End.mul_apply]

theorem operatorAnnihilation_sq :
    operatorAnnihilation (W := W) * operatorAnnihilation = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorAnnihilation, Matrix.mul_apply, Fin.sum_univ_two,
      Module.End.mul_apply]

theorem operatorCreation_annihilation_anticommutator :
    operatorCreation (W := W) * operatorAnnihilation +
        operatorAnnihilation * operatorCreation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorCreation, operatorAnnihilation, Matrix.mul_apply,
      Fin.sum_univ_two, Module.End.mul_apply]

def operatorNumber : OperatorMatrix W :=
  operatorCreation * operatorAnnihilation

theorem operatorNumber_idempotent :
    operatorNumber (W := W) * operatorNumber = operatorNumber := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorNumber, operatorCreation, operatorAnnihilation,
      Matrix.mul_apply, Fin.sum_univ_two, Module.End.mul_apply]

theorem operatorNumber_creation_commutator :
    operatorNumber (W := W) * operatorCreation -
        operatorCreation * operatorNumber = operatorCreation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorNumber, operatorCreation, operatorAnnihilation,
      Matrix.mul_apply, Fin.sum_univ_two, Module.End.mul_apply]

theorem operatorNumber_annihilation_commutator :
    operatorNumber (W := W) * operatorAnnihilation -
        operatorAnnihilation * operatorNumber = -operatorAnnihilation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorNumber, operatorCreation, operatorAnnihilation,
      Matrix.mul_apply, Fin.sum_univ_two, Module.End.mul_apply]

theorem operatorCommutator_number_creation :
    operatorCommutator (operatorNumber (W := W)) operatorCreation =
      operatorCreation := by
  exact operatorNumber_creation_commutator

theorem operatorCommutator_number_annihilation :
    operatorCommutator (operatorNumber (W := W)) operatorAnnihilation =
      -operatorAnnihilation := by
  exact operatorNumber_annihilation_commutator

lemma two_smul_complex (x : W) : (2 : ℂ) • x = x + x := by
  have h : (2 : ℂ) = 1 + 1 := by norm_num
  rw [h, add_smul, one_smul]

lemma neg_two_smul_complex (x : W) : (-2 : ℂ) • x = -x - x := by
  have h : (-2 : ℂ) = -1 + -1 := by norm_num
  rw [h, add_smul, neg_smul, one_smul, sub_eq_add_neg]

theorem operatorCommutator_parity_creation :
    operatorCommutator (operatorParity (W := W)) operatorCreation =
      (2 : ℂ) • operatorCreation := by
  have h₁ : operatorParity (W := W) * operatorCreation = operatorCreation := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [operatorParity, operatorCreation, Matrix.mul_apply,
        Fin.sum_univ_two, Module.End.mul_apply]
  have h₂ : operatorCreation * operatorParity (W := W) = -operatorCreation := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [operatorParity, operatorCreation, Matrix.mul_apply,
        Fin.sum_univ_two, Module.End.mul_apply]
  rw [operatorCommutator, h₁, h₂]
  rw [sub_neg_eq_add, ← two_smul_complex]

theorem operatorCommutator_parity_annihilation :
    operatorCommutator (operatorParity (W := W)) operatorAnnihilation =
      (-2 : ℂ) • operatorAnnihilation := by
  have h₁ : operatorParity (W := W) * operatorAnnihilation =
      -operatorAnnihilation := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [operatorParity, operatorAnnihilation, Matrix.mul_apply,
        Fin.sum_univ_two, Module.End.mul_apply]
  have h₂ : operatorAnnihilation * operatorParity (W := W) =
      operatorAnnihilation := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [operatorParity, operatorAnnihilation, Matrix.mul_apply,
        Fin.sum_univ_two, Module.End.mul_apply]
  rw [operatorCommutator, h₁, h₂]
  rw [sub_eq_add_neg, ← neg_add, ← two_smul_complex, neg_smul]

def doubledCreation : Module.End ℂ (Fin 2 → W) :=
  InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorCreation

def doubledAnnihilation : Module.End ℂ (Fin 2 → W) :=
  InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorAnnihilation

theorem doubledCreation_sq : doubledCreation (W := W) * doubledCreation = 0 := by
  change InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorCreation *
      InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorCreation = 0
  rw [← InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_mul_end,
    operatorCreation_sq]
  apply LinearMap.ext
  intro v
  exact InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_zero v

theorem doubledAnnihilation_sq :
    doubledAnnihilation (W := W) * doubledAnnihilation = 0 := by
  change InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorAnnihilation *
      InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorAnnihilation = 0
  rw [← InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_mul_end,
    operatorAnnihilation_sq]
  apply LinearMap.ext
  intro v
  exact InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_zero v

theorem doubledCreation_annihilation_anticommutator :
    doubledCreation (W := W) * doubledAnnihilation +
        doubledAnnihilation * doubledCreation = 1 := by
  change
    InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorCreation *
          InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorAnnihilation +
        InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorAnnihilation *
          InfoGeometry.Optics.OperatorLiftCarrier.matrixAction operatorCreation = 1
  rw [← InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_mul_end,
    ← InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_mul_end,
    ← InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_add,
    operatorCreation_annihilation_anticommutator]
  apply LinearMap.ext
  intro v
  exact InfoGeometry.Optics.OperatorLiftCarrier.matrixAction_one v

end
end InfoGeometry.Optics.ChiralLorentzOperatorLift
