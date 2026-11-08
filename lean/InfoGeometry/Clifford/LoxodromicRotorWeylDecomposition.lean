import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

noncomputable section

namespace InfoGeometry.Clifford.LoxodromicRotorWeylDecomposition

open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
open InfoGeometry.Clifford.STAOperators
open InfoGeometry.Clifford.CrawfordDiracBispinorDensities

abbrev Operator := ChiralGrandCanonicalLoxodromicRotor.Operator

def complexStructure : Operator := boostAxis * phaseAxis

theorem complexStructure_sq :
    complexStructure * complexStructure = -(1 : Operator) := by
  unfold complexStructure
  calc
    (boostAxis * phaseAxis) * (boostAxis * phaseAxis) =
        (boostAxis * boostAxis) * (phaseAxis * phaseAxis) := by
          calc
            (boostAxis * phaseAxis) * (boostAxis * phaseAxis) =
                boostAxis * (phaseAxis * boostAxis) * phaseAxis := by
                  simp [Matrix.mul_assoc]
            _ = boostAxis * (boostAxis * phaseAxis) * phaseAxis := by
                  rw [boostAxis_phaseAxis_commute]
            _ = (boostAxis * boostAxis) * (phaseAxis * phaseAxis) := by
                  simp [Matrix.mul_assoc]
    _ = -(1 : Operator) := by rw [boostAxis_sq, phaseAxis_sq]; simp

def projectorPlus : Operator :=
  (1 / 2 : ℂ) • ((1 : Operator) - Complex.I • complexStructure)

def projectorMinus : Operator :=
  (1 / 2 : ℂ) • ((1 : Operator) + Complex.I • complexStructure)

theorem algebraMap_complexI_sq :
    (algebraMap ℂ Operator Complex.I) * algebraMap ℂ Operator Complex.I =
      -(1 : Operator) := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

theorem projectorPlus_add_projectorMinus :
    projectorPlus + projectorMinus = (1 : Operator) := by
  unfold projectorPlus projectorMinus
  simp only [smul_add, smul_sub, smul_smul, Complex.I_sq]
  module

theorem projectorPlus_mul_projectorMinus :
    projectorPlus * projectorMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorPlus, projectorMinus, complexStructure, boostAxis,
      phaseAxis, staSigma3, staPhaseBivector, gamma0, gamma1, gamma2,
      gamma3, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

theorem projectorMinus_mul_projectorPlus :
    projectorMinus * projectorPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorPlus, projectorMinus, complexStructure, boostAxis,
      phaseAxis, staSigma3, staPhaseBivector, gamma0, gamma1, gamma2,
      gamma3, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

theorem projectorPlus_idempotent :
    projectorPlus * projectorPlus = projectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorPlus, complexStructure, boostAxis, phaseAxis,
      staSigma3, staPhaseBivector, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

theorem projectorMinus_idempotent :
    projectorMinus * projectorMinus = projectorMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorMinus, complexStructure, boostAxis, phaseAxis,
      staSigma3, staPhaseBivector, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

theorem complexStructure_mul_projectorPlus :
    complexStructure * projectorPlus = Complex.I • projectorPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorPlus, complexStructure, boostAxis, phaseAxis,
      staSigma3, staPhaseBivector, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

theorem complexStructure_mul_projectorMinus :
    complexStructure * projectorMinus = -(Complex.I • projectorMinus) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projectorMinus, complexStructure, boostAxis, phaseAxis,
      staSigma3, staPhaseBivector, gamma0, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;> norm_num <;> ring

end InfoGeometry.Clifford.LoxodromicRotorWeylDecomposition
