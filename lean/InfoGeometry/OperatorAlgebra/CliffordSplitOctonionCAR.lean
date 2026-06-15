import Mathlib.Tactic
import InfoGeometry.Algebraic.SplitQuadraticForm

/-!
# Cl(4,4) CAR algebra — 4 fermionic modes

A kernel-checked CAR interface inside the real split Clifford algebra for
`splitQuadraticForm 4`.
-/

open CliffordAlgebra
open InfoGeometry.Algebraic.SplitSignature

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

abbrev Cl44 := CliffordAlgebra (splitQuadraticForm 4)
abbrev Q44 := splitQuadraticForm 4

def pVec (i : Fin 4) : SplitModule 4 := splitBasisVector (Sum.inl i)
def nVec (i : Fin 4) : SplitModule 4 := splitBasisVector (Sum.inr i)

def p (i : Fin 4) : Cl44 := ι Q44 (pVec i)
def n (i : Fin 4) : Cl44 := ι Q44 (nVec i)

@[simp] theorem p_sq (i : Fin 4) : p i * p i = 1 := by
  calc
    p i * p i = algebraMap ℝ Cl44 (Q44 (pVec i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ Cl44 (1 : ℝ) := by
      rw [Q44, pVec, splitQuadraticForm_posBasisVector]
    _ = 1 := by simp

@[simp] theorem n_sq (i : Fin 4) : n i * n i = -1 := by
  calc
    n i * n i = algebraMap ℝ Cl44 (Q44 (nVec i)) := ι_sq_scalar _ _
    _ = algebraMap ℝ Cl44 (-1 : ℝ) := by
      rw [Q44, nVec, splitQuadraticForm_negBasisVector]
    _ = -1 := by simp

theorem p_n_anticomm (i j : Fin 4) : p i * n j + n j * p i = 0 := by
  have h : QuadraticMap.polar Q44 (pVec i) (nVec j) = 0 := by
    fin_cases i <;> fin_cases j <;> rw [QuadraticMap.polar] <;>
      simp [Q44, pVec, nVec, splitQuadraticForm, splitBasisVector]
  rw [p, n, ι_mul_ι_add_swap, h]
  simp

theorem p_p_anticomm (i j : Fin 4) (hij : i ≠ j) : p i * p j + p j * p i = 0 := by
  have h : QuadraticMap.polar Q44 (pVec i) (pVec j) = 0 := by
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      rw [QuadraticMap.polar] <;>
      simp [Q44, pVec, splitQuadraticForm, splitBasisVector, Fin.sum_univ_four]
  change ι Q44 (pVec i) * ι Q44 (pVec j) + ι Q44 (pVec j) * ι Q44 (pVec i) = 0
  rw [ι_mul_ι_add_swap, h]
  simp

theorem n_n_anticomm (i j : Fin 4) (hij : i ≠ j) : n i * n j + n j * n i = 0 := by
  have h : QuadraticMap.polar Q44 (nVec i) (nVec j) = 0 := by
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      rw [QuadraticMap.polar] <;>
      simp [Q44, nVec, splitQuadraticForm, splitBasisVector, Fin.sum_univ_four]
  change ι Q44 (nVec i) * ι Q44 (nVec j) + ι Q44 (nVec j) * ι Q44 (nVec i) = 0
  rw [ι_mul_ι_add_swap, h]
  simp

def aVec (i : Fin 4) : SplitModule 4 := (1 / 2 : ℝ) • (pVec i + nVec i)
def aDagVec (i : Fin 4) : SplitModule 4 := (1 / 2 : ℝ) • (pVec i - nVec i)

def a (i : Fin 4) : Cl44 := ι Q44 (aVec i)
def aDag (i : Fin 4) : Cl44 := ι Q44 (aDagVec i)

@[simp] theorem Q_aVec (i : Fin 4) : Q44 (aVec i) = 0 := by
  fin_cases i <;>
    simp [Q44, aVec, pVec, nVec, splitQuadraticForm, splitBasisVector]

@[simp] theorem Q_aDagVec (i : Fin 4) : Q44 (aDagVec i) = 0 := by
  fin_cases i <;>
    simp [Q44, aDagVec, pVec, nVec, splitQuadraticForm, splitBasisVector]

@[simp] theorem a_sq_zero (i : Fin 4) : a i * a i = 0 := by
  rw [a, ι_sq_scalar, Q_aVec]
  simp

@[simp] theorem aDag_sq_zero (i : Fin 4) : aDag i * aDag i = 0 := by
  rw [aDag, ι_sq_scalar, Q_aDagVec]
  simp

theorem polar_a_aDag (i j : Fin 4) :
    QuadraticMap.polar Q44 (aVec i) (aDagVec j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rw [QuadraticMap.polar] <;>
    simp [Q44, aVec, aDagVec, pVec, nVec, splitQuadraticForm, splitBasisVector, Fin.sum_univ_four] <;>
    norm_num

/-- Polar pairing of two annihilation vectors. -/
theorem polar_a_a_polar (i j : Fin 4) :
    QuadraticMap.polar Q44 (aVec i) (aVec j) = 0 := by
  fin_cases i <;> fin_cases j <;> rw [QuadraticMap.polar] <;>
    simp [Q44, aVec, pVec, nVec, splitQuadraticForm, splitBasisVector, Fin.sum_univ_four] <;>
    norm_num

/-- Polar pairing of two creation vectors. -/
theorem polar_aDag_aDag_polar (i j : Fin 4) :
    QuadraticMap.polar Q44 (aDagVec i) (aDagVec j) = 0 := by
  fin_cases i <;> fin_cases j <;> rw [QuadraticMap.polar] <;>
    simp [Q44, aDagVec, pVec, nVec, splitQuadraticForm, splitBasisVector, Fin.sum_univ_four] <;>
    norm_num

theorem car_identity (i j : Fin 4) :
    a i * aDag j + aDag j * a i = (if i = j then (1 : Cl44) else 0) := by
  rw [a, aDag, ι_mul_ι_add_swap, polar_a_aDag]
  split_ifs <;> simp

theorem a_a_anticomm (i j : Fin 4) : a i * a j + a j * a i = 0 := by
  by_cases hij : i = j
  · subst j; simp [a_sq_zero]
  · dsimp [a]; rw [ι_mul_ι_add_swap, polar_a_a_polar]; simp

theorem aDag_aDag_anticomm (i j : Fin 4) : aDag i * aDag j + aDag j * aDag i = 0 := by
  by_cases hij : i = j
  · subst j; simp [aDag_sq_zero]
  · dsimp [aDag]; rw [ι_mul_ι_add_swap, polar_aDag_aDag_polar]; simp

/-- Complete CAR packet for 4 fermionic modes from Cl(4,4). -/
theorem car_packet :
    (∀ i : Fin 4, a i * a i = 0) ∧
    (∀ i : Fin 4, aDag i * aDag i = 0) ∧
    (∀ i j : Fin 4, a i * a j + a j * a i = 0) ∧
    (∀ i j : Fin 4, aDag i * aDag j + aDag j * aDag i = 0) ∧
    (∀ i j : Fin 4,
      a i * aDag j + aDag j * a i = if i = j then (1 : Cl44) else 0) := by
  exact ⟨a_sq_zero, aDag_sq_zero, a_a_anticomm, aDag_aDag_anticomm, car_identity⟩

end InfoGeometry.OperatorAlgebra.CliffordCAR
