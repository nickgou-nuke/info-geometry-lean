import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Noncommutative `Cl(5,5)` projective boundary packet

This owner is the operator-algebraic boundary construction.  It is separate
from `Cl55ProjectiveBoundary`, which records a projectivized quadratic-form
model.  No coordinate model is used here: the boundary packet is built from
the fifth positive/negative Clifford pair in an abstract ring.
-/

variable {A : Type*} [Ring A] [Algebra ℚ A]

namespace InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

class OperatorCl55 (e f : Fin 5 → A) : Prop where
  e_sq : ∀ i, e i * e i = 1
  f_sq : ∀ i, f i * f i = -1
  e_anti : ∀ i j, i ≠ j → e i * e j + e j * e i = 0
  f_anti : ∀ i j, i ≠ j → f i * f j + f j * f i = 0
  ef_anti : ∀ i j, e i * f j + f j * e i = 0

variable {e f : Fin 5 → A} [hCl : OperatorCl55 e f]

def half : A := algebraMap ℚ A (1 / 2)
def quarter : A := algebraMap ℚ A (1 / 4)

lemma half_mul_half : half (A := A) * half (A := A) = quarter (A := A) := by
  unfold half quarter
  rw [← map_mul]
  norm_num

lemma quarter_mul_four : quarter (A := A) * (1 + 1 + 1 + 1) = 1 := by
  unfold quarter
  have h4 : (1 + 1 + 1 + 1 : A) = algebraMap ℚ A 4 := by
    norm_num
    exact (map_ofNat (algebraMap ℚ A) 4).symm
  rw [h4, ← map_mul]
  norm_num

def annihilator (e f : Fin 5 → A) (i : Fin 5) : A :=
  half * (e i + f i)

def creator (e f : Fin 5 → A) (i : Fin 5) : A :=
  half * (e i - f i)

def boundaryAnnihilator (e f : Fin 5 → A) : A := annihilator e f 4
def boundaryCreator (e f : Fin 5 → A) : A := creator e f 4

abbrev witt_a_55 (e f : Fin 5 → A) (i : Fin 5) : A := annihilator e f i
abbrev witt_c_55 (e f : Fin 5 → A) (i : Fin 5) : A := creator e f i
abbrev projective_compensation_a (e f : Fin 5 → A) : A := boundaryAnnihilator e f
abbrev projective_compensation_c (e f : Fin 5 → A) : A := boundaryCreator e f

omit [Algebra ℚ A] in
lemma ef_anti_symm_55 (i j : Fin 5) : e i * f j = - (f j * e i) := by
  have h := hCl.ef_anti i j
  calc
    e i * f j = e i * f j + f j * e i - f j * e i := by rw [add_sub_cancel_right]
    _ = 0 - f j * e i := by rw [h]
    _ = - (f j * e i) := by rw [zero_sub]

theorem boundaryAnnihilator_sq : boundaryAnnihilator e f * boundaryAnnihilator e f = 0 := by
  unfold boundaryAnnihilator annihilator
  have he : e 4 * e 4 = 1 := hCl.e_sq 4
  have hf : f 4 * f 4 = -1 := hCl.f_sq 4
  have hef : e 4 * f 4 + f 4 * e 4 = 0 := hCl.ef_anti 4 4
  have hcomm : half (A := A) * (e 4 + f 4) =
      (e 4 + f 4) * half (A := A) := Algebra.commutes _ _
  calc
    (half * (e 4 + f 4)) * (half * (e 4 + f 4)) =
        half * ((e 4 + f 4) * half) * (e 4 + f 4) := by
      simp only [mul_assoc]
    _ = half * (half * (e 4 + f 4)) * (e 4 + f 4) := by rw [← hcomm]
    _ = (half * half) * ((e 4 + f 4) * (e 4 + f 4)) := by
      simp only [mul_assoc]
    _ = (half * half) *
        (e 4 * e 4 + e 4 * f 4 + f 4 * e 4 + f 4 * f 4) := by
      congr 1
      rw [mul_add, add_mul, add_mul]
      abel
    _ = (half * half) * (1 + 0 + -1) := by
      have h : e 4 * e 4 + e 4 * f 4 + f 4 * e 4 + f 4 * f 4 =
          e 4 * e 4 + (e 4 * f 4 + f 4 * e 4) + f 4 * f 4 := by abel
      rw [h, he, hef, hf]
    _ = 0 := by simp

theorem boundaryCreator_sq : boundaryCreator e f * boundaryCreator e f = 0 := by
  unfold boundaryCreator creator
  have he : e 4 * e 4 = 1 := hCl.e_sq 4
  have hf : f 4 * f 4 = -1 := hCl.f_sq 4
  have hef : e 4 * f 4 + f 4 * e 4 = 0 := hCl.ef_anti 4 4
  have hcomm : half (A := A) * (e 4 - f 4) =
      (e 4 - f 4) * half (A := A) := Algebra.commutes _ _
  calc
    (half * (e 4 - f 4)) * (half * (e 4 - f 4)) =
        half * ((e 4 - f 4) * half) * (e 4 - f 4) := by
      simp only [mul_assoc]
    _ = half * (half * (e 4 - f 4)) * (e 4 - f 4) := by rw [← hcomm]
    _ = (half * half) * ((e 4 - f 4) * (e 4 - f 4)) := by
      simp only [mul_assoc]
    _ = (half * half) *
        (e 4 * e 4 - (e 4 * f 4 + f 4 * e 4) + f 4 * f 4) := by
      congr 1
      rw [mul_sub, sub_mul, sub_mul]
      abel
    _ = (half * half) * (1 - 0 + -1) := by rw [he, hef, hf]
    _ = 0 := by simp

theorem boundary_car :
    boundaryAnnihilator e f * boundaryAnnihilator e f = 0 ∧
    boundaryCreator e f * boundaryCreator e f = 0 ∧
    boundaryAnnihilator e f * boundaryCreator e f +
        boundaryCreator e f * boundaryAnnihilator e f = 1 := by
  have ha := boundaryAnnihilator_sq (e := e) (f := f)
  have hc := boundaryCreator_sq (e := e) (f := f)
  unfold boundaryAnnihilator boundaryCreator annihilator creator
  have he : e 4 * e 4 = 1 := hCl.e_sq 4
  have hf : f 4 * f 4 = -1 := hCl.f_sq 4
  have hef : e 4 * f 4 + f 4 * e 4 = 0 := hCl.ef_anti 4 4
  have hcommPlus : half (A := A) * (e 4 + f 4) =
      (e 4 + f 4) * half (A := A) := Algebra.commutes _ _
  have hcommMinus : half (A := A) * (e 4 - f 4) =
      (e 4 - f 4) * half (A := A) := Algebra.commutes _ _
  refine ⟨ha, hc, ?_⟩
  calc
    (half * (e 4 + f 4)) * (half * (e 4 - f 4)) +
        (half * (e 4 - f 4)) * (half * (e 4 + f 4)) =
        (half * half) * ((e 4 + f 4) * (e 4 - f 4) +
          (e 4 - f 4) * (e 4 + f 4)) := by
      rw [show (half * (e 4 + f 4)) * (half * (e 4 - f 4)) =
          (half * half) * ((e 4 + f 4) * (e 4 - f 4)) by
            calc
              _ = half * ((e 4 + f 4) * half) * (e 4 - f 4) := by simp only [mul_assoc]
              _ = half * (half * (e 4 + f 4)) * (e 4 - f 4) := by rw [← hcommPlus]
              _ = _ := by simp only [mul_assoc],
        show (half * (e 4 - f 4)) * (half * (e 4 + f 4)) =
          (half * half) * ((e 4 - f 4) * (e 4 + f 4)) by
            calc
              _ = half * ((e 4 - f 4) * half) * (e 4 + f 4) := by simp only [mul_assoc]
              _ = half * (half * (e 4 - f 4)) * (e 4 + f 4) := by rw [← hcommMinus]
              _ = _ := by simp only [mul_assoc]]
      rw [← mul_add]
    _ = quarter * ((e 4 + f 4) * (e 4 - f 4) +
        (e 4 - f 4) * (e 4 + f 4)) := by rw [half_mul_half]
    _ = quarter * (1 + 1 + 1 + 1) := by
      have h : (e 4 + f 4) * (e 4 - f 4) +
          (e 4 - f 4) * (e 4 + f 4) = 1 + 1 + 1 + 1 := by
        rw [mul_sub, add_mul, add_mul, mul_add, sub_mul, sub_mul]
        rw [he, hf]
        abel
      rw [h]
    _ = 1 := quarter_mul_four

theorem projective_compensation_anticomm :
    projective_compensation_a e f * projective_compensation_c e f +
        projective_compensation_c e f * projective_compensation_a e f = 1 := by
  exact (boundary_car (e := e) (f := f)).2.2

theorem projective_compensation_a_sq :
    projective_compensation_a e f * projective_compensation_a e f = 0 :=
  boundaryAnnihilator_sq (e := e) (f := f)

theorem projective_compensation_c_sq :
    projective_compensation_c e f * projective_compensation_c e f = 0 :=
  boundaryCreator_sq (e := e) (f := f)

end InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary
