import InfoGeometry.Canonical.Cl55WittLieRouting
import Mathlib.LinearAlgebra.Eigenspace.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace InfoGeometry.Canonical.Cl55WittLieRouting

open scoped Matrix Kronecker
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR

/-! The Cartan grading is defined by the ordinary commutator with the
diagonal number operator.  The five native Witt packets are then subspaces of
the corresponding eigenspaces.  This file does not identify the resulting
Lie algebra with a named real form. -/

lemma sum_if_eq {α : Type*} [AddCommMonoid α]
    (f : Fin 5 → α) (k : Fin 5) :
    ∑ i : Fin 5, (if i = k then f i else 0) = f k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · simp

theorem adNumber_creation (k : Fin 5) :
    numberAdjoint (creation k) = creation k := by
  change bracket numberOperator (creation k) = creation k
  unfold numberOperator
  rw [show (∑ i : Fin 5, E i i) =
      ∑ i : Fin 5, (1 : ℝ) • E i i by simp]
  rw [bracket_sum_left]
  simp_rw [E_creation]
  simpa [sum_if_eq]

theorem adNumber_annihilation (k : Fin 5) :
    numberAdjoint (annihilation k) = -annihilation k := by
  change bracket numberOperator (annihilation k) = -annihilation k
  unfold numberOperator
  rw [show (∑ i : Fin 5, E i i) =
      ∑ i : Fin 5, (1 : ℝ) • E i i by simp]
  rw [bracket_sum_left]
  simp_rw [E_annihilation]
  have h := sum_if_eq (fun i : Fin 5 => -annihilation k) k
  simpa [sum_if_eq]

theorem adNumber_E (k l : Fin 5) :
    numberAdjoint (E k l) = 0 := by
  change bracket numberOperator (E k l) = 0
  unfold numberOperator
  rw [show (∑ i : Fin 5, E i i) =
      ∑ i : Fin 5, (1 : ℝ) • E i i by simp]
  rw [bracket_sum_left]
  simp_rw [E_bracket]
  simp

theorem adNumber_creation_quadratic (i j : Fin 5) :
    numberAdjoint (creation i * creation j) =
      (2 : ℝ) • (creation i * creation j) := by
  change bracket numberOperator (creation i * creation j) = _
  rw [bracket_mul_right]
  have hi : bracket numberOperator (creation i) = creation i := adNumber_creation i
  have hj : bracket numberOperator (creation j) = creation j := adNumber_creation j
  rw [hi, hj]
  rw [two_smul]

theorem adNumber_annihilation_quadratic (i j : Fin 5) :
    numberAdjoint (annihilation i * annihilation j) =
      (-2 : ℝ) • (annihilation i * annihilation j) := by
  change bracket numberOperator (annihilation i * annihilation j) = _
  rw [bracket_mul_right]
  have hi : bracket numberOperator (annihilation i) = -annihilation i :=
    adNumber_annihilation i
  have hj : bracket numberOperator (annihilation j) = -annihilation j :=
    adNumber_annihilation j
  rw [hi, hj]
  simp only [neg_mul, mul_neg]
  rw [← neg_add]
  simp [two_smul]

def wittFiveGrade : Submodule ℝ (MatStage 5) :=
  (wittNegTwo ⊔ wittNegOne) ⊔ wittZero ⊔ wittPosOne ⊔ wittPosTwo

end InfoGeometry.Canonical.Cl55WittLieRouting
