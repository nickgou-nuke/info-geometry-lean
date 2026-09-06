import Mathlib
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered
import InfoGeometry.Algebra.Cl11OSp12

/-!
# Matrix CAR Surface for OSp(1|2)

This file applies the fundamental `cl11MatrixBridge` to push the abstract 
Clifford algebraic CAR (Canonical Anticommutation Relation) surface of the 
fermionic oscillators directly into the $2 \times 2$ real matrix representations.

It provides a concrete `FermionicCARSurface` for use in the bounded 
operator representations of `OSp(1|2)`.
-/

namespace InfoGeometry.Recovered

open InfoGeometry.SplitQuaternion
open InfoGeometry.Algebra.Cl11OSp12
open Cl11OSp12

noncomputable section

/-- The $2 \times 2$ real matrix representation of the annihilation symbol. -/
def matrix_b : Matrix (Fin 2) (Fin 2) ℝ := cl11MatrixBridge b

/-- The $2 \times 2$ real matrix representation of the creation symbol. -/
def matrix_bdag : Matrix (Fin 2) (Fin 2) ℝ := cl11MatrixBridge bdag

lemma matrix_b_sq : matrix_b * matrix_b = 0 := by
  calc
    matrix_b * matrix_b = cl11MatrixBridge b * cl11MatrixBridge b := rfl
    _ = cl11MatrixBridge (b * b) := by rw [← map_mul]
    _ = cl11MatrixBridge 0 := by rw [b_sq]
    _ = 0 := by rw [map_zero]

lemma matrix_bdag_sq : matrix_bdag * matrix_bdag = 0 := by
  calc
    matrix_bdag * matrix_bdag = cl11MatrixBridge bdag * cl11MatrixBridge bdag := rfl
    _ = cl11MatrixBridge (bdag * bdag) := by rw [← map_mul]
    _ = cl11MatrixBridge 0 := by rw [bdag_sq]
    _ = 0 := by rw [map_zero]

lemma matrix_anticomm : matrix_b * matrix_bdag + matrix_bdag * matrix_b = 1 := by
  calc
    matrix_b * matrix_bdag + matrix_bdag * matrix_b
      = cl11MatrixBridge b * cl11MatrixBridge bdag + cl11MatrixBridge bdag * cl11MatrixBridge b := rfl
    _ = cl11MatrixBridge (b * bdag) + cl11MatrixBridge (bdag * b) := by rw [← map_mul, ← map_mul]
    _ = cl11MatrixBridge (b * bdag + bdag * b) := by rw [← map_add]
    _ = cl11MatrixBridge 1 := by rw [anticomm_bbdag]
    _ = 1 := by rw [map_one]

/--
The concrete matrix realization of the Fermionic CAR Surface using 
the explicit metric projection mappings from the abstract $Cl(1,1)$ basis.
-/
def splitMatrixCARSurface : FermionicCARSurface (Matrix (Fin 2) (Fin 2) ℝ) where
  b := matrix_b
  bdag := matrix_bdag
  b_sq := matrix_b_sq
  bdag_sq := matrix_bdag_sq
  anticomm := matrix_anticomm

end InfoGeometry.Recovered
