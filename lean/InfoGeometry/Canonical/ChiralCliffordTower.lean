import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix

set_option linter.unusedSimpArgs false

namespace InfoGeometry.CliffordTower

variable {R : Type*} [CommRing R]

def e_null : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1;
     0, 0]

def f_null : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0;
     1, 0]

def krein_eta : Matrix (Fin 2) (Fin 2) R :=
  !![1,  0;
     0, -1]

@[simp] theorem e_null_sq : (e_null : Matrix (Fin 2) (Fin 2) R) * e_null = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_null, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem f_null_sq : (f_null : Matrix (Fin 2) (Fin 2) R) * f_null = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [f_null, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ef_anticommutator :
    (e_null : Matrix (Fin 2) (Fin 2) R) * f_null + f_null * e_null = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e_null, f_null, Matrix.mul_apply, Fin.sum_univ_succ]

theorem krein_eta_is_commutator :
    (krein_eta : Matrix (Fin 2) (Fin 2) R) = e_null * f_null - f_null * e_null := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [krein_eta, e_null, f_null, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem krein_eta_sq :
    (krein_eta : Matrix (Fin 2) (Fin 2) R) * krein_eta = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [krein_eta, Matrix.mul_apply, Fin.sum_univ_succ]

def kron2 (A B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j =>
    let i_R : Fin 2 := ⟨i.val / 2, by omega⟩
    let i_L : Fin 2 := ⟨i.val % 2, by omega⟩
    let j_R : Fin 2 := ⟨j.val / 2, by omega⟩
    let j_L : Fin 2 := ⟨j.val % 2, by omega⟩
    A i_R j_R * B i_L j_L

lemma kron2_mul (A₁ A₂ B₁ B₂ : Matrix (Fin 2) (Fin 2) R) :
    kron2 (A₁ * A₂) (B₁ * B₂) = kron2 A₁ B₁ * kron2 A₂ B₂ := by
  ext i j
  dsimp [kron2, Matrix.mul_apply]
  revert i j
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, Fin.sum_univ_succ] <;> ring

def e_R : Matrix (Fin 4) (Fin 4) R := kron2 e_null 1

def e_L : Matrix (Fin 4) (Fin 4) R := kron2 1 e_null

def eta_tot : Matrix (Fin 4) (Fin 4) R := kron2 krein_eta krein_eta

@[simp] theorem e_R_sq : (e_R : Matrix (Fin 4) (Fin 4) R) * e_R = 0 := by
  dsimp [e_R]
  rw [← kron2_mul, e_null_sq, mul_one]
  ext i j; dsimp [kron2]; rw [zero_mul]

@[simp] theorem e_L_sq : (e_L : Matrix (Fin 4) (Fin 4) R) * e_L = 0 := by
  dsimp [e_L]
  rw [← kron2_mul, mul_one, e_null_sq]
  ext i j; dsimp [kron2]; rw [mul_zero]

theorem e_R_comm_e_L :
    (e_R : Matrix (Fin 4) (Fin 4) R) * e_L = e_L * e_R := by
  dsimp [e_R, e_L]
  rw [← kron2_mul, ← kron2_mul]
  simp

def chiralBivector : Matrix (Fin 4) (Fin 4) R :=
  e_R * e_L

theorem chiral_bivector_on_shell :
    (chiralBivector : Matrix (Fin 4) (Fin 4) R) * chiralBivector = 0 := by
  dsimp [chiralBivector]
  rw [mul_assoc e_R e_L (e_R * e_L)]
  rw [← mul_assoc e_L e_R e_L]
  rw [← e_R_comm_e_L]
  rw [mul_assoc e_R e_L e_L]
  rw [← mul_assoc e_R e_R (e_L * e_L)]
  rw [e_R_sq, zero_mul]

theorem eta_tot_involutive :
    (eta_tot : Matrix (Fin 4) (Fin 4) R) * eta_tot = 1 := by
  dsimp [eta_tot]
  rw [← kron2_mul, krein_eta_sq]
  ext i j
  dsimp [kron2]
  fin_cases i <;> fin_cases j <;> simp

end InfoGeometry.CliffordTower
