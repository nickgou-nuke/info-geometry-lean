import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The finite split-Clifford/projective matrix bridge

This owner records the concrete real matrix atom behind the Witt basis.  It
proves the nilpotent CAR relations, the complementary coordinate projectors,
the split Cartan action, and its induced dilation on the affine projective
coordinate.  It does not identify a quotient with `ℝP¹` or `ℂP¹`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def e0 : M2R := !![0, 1; 1, 0]

def e1 : M2R := !![0, 1; -1, 0]

def b : M2R := (1 / 2 : ℝ) • (e0 + e1)

def bdag : M2R := (1 / 2 : ℝ) • (e0 - e1)

def cartan : M2R := e0 * e1

def Pminus : M2R := b * bdag

def Pplus : M2R := bdag * b

theorem e0_sq : e0 * e0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, Matrix.mul_apply, Fin.sum_univ_two]

theorem e1_sq : e1 * e1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem e0_e1_anticomm : e0 * e1 + e1 * e0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem b_sq : b * b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bdag_sq : bdag * bdag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem b_bdag_add_bdag_b : b * bdag + bdag * b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_sq : cartan * cartan = 1 := by
  unfold cartan
  calc
    (e0 * e1) * (e0 * e1) = -(e0 * e0) * (e1 * e1) := by
      have h : e1 * e0 = -(e0 * e1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [e0, e1, Matrix.mul_apply, Fin.sum_univ_two]
      rw [show (e0 * e1) * (e0 * e1) = e0 * (e1 * e0) * e1 by noncomm_ring, h]
      noncomm_ring
    _ = 1 := by rw [e0_sq, e1_sq]; simp

theorem Pminus_eq_first_coordinate_projector :
    Pminus = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pminus, b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Pplus_eq_second_coordinate_projector :
    Pplus = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pplus, b, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Pminus_sq : Pminus * Pminus = Pminus := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pplus_sq : Pplus * Pplus = Pplus := by
  rw [Pplus_eq_second_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Pminus_add_Pplus : Pminus + Pplus = 1 := by
  rw [Pminus_eq_first_coordinate_projector, Pplus_eq_second_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cartan_eq_Pplus_sub_Pminus : cartan = Pplus - Pminus := by
  rw [Pplus_eq_second_coordinate_projector, Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem cartan_mul_b : cartan * b = -b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem b_mul_cartan : b * cartan = b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_commutator_b : cartan * b - b * cartan = -2 • b := by
  rw [cartan_mul_b, b_mul_cartan]
  module

theorem cartan_mul_bdag : cartan * bdag = bdag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bdag_mul_cartan : bdag * cartan = -bdag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartan, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cartan_commutator_bdag : cartan * bdag - bdag * cartan = 2 • bdag := by
  rw [cartan_mul_bdag, bdag_mul_cartan]
  module

end InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge

