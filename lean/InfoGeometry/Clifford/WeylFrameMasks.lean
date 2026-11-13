/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.OperatorAlgebra.FiniteOperatorFrame
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Matrix.Basis

/-!
# Weyl twirling and finite Peirce-window masks

The four existing Jones generators give a unitary family over any star ring.
The convention for its fourth entry is `-K_mat`. Its conjugation sum is a
scalar matrix whose diagonal entry is twice the sum of the two original
diagonal entries. This is a statement about the image of the scalar embedding;
the resulting matrix need not be central when the coefficient ring is
noncommutative. The unnormalized twirl satisfies `E (E M) = 4 • E M`.

Applying the generators to a single Peirce window gives four atoms, with two
copies of each of two matrix units. A balanced pair has frame sum `1`; the
parallel pair has frame sum `P + P`. Thus equal selection cardinality alone
does not determine the retained operator. These finite masks do not assert
metric porosity or an analytic fractal uncertainty estimate.
-/

namespace InfoGeometry.Clifford.WeylFrameMasks

open Matrix
open scoped BigOperators
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
open InfoGeometry.OperatorAlgebra.FiniteOperatorFrame

variable {B : Type*} [Ring B] [StarRing B]

/-- The Jones/Weyl family, with the attachment's `Ω = -K` convention. -/
def weylFamily : Fin 4 → Matrix (Fin 2) (Fin 2) B :=
  ![I_mat, Gamma_mat, J_mat, -K_mat]

/-- Every member is a native unitary, including the skew generator `-K`. -/
theorem weylFamily_mem_unitary (k : Fin 4) :
    weylFamily (B := B) k ∈ unitary (Matrix (Fin 2) (Fin 2) B) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [weylFamily, I_mat, Gamma_mat, J_mat, K_mat, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_succ]

/-- The first diagonal matrix unit is the Peirce window. -/
def peirceWindow : Matrix (Fin 2) (Fin 2) B :=
  Matrix.single 0 0 1

theorem peirceWindow_isStarProjection :
    IsStarProjection (peirceWindow (B := B)) where
  isIdempotentElem := by
    change peirceWindow * peirceWindow = peirceWindow (B := B)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peirceWindow, Matrix.single, Matrix.mul_apply]
  isSelfAdjoint := by
    change (peirceWindow (B := B))ᴴ = peirceWindow
    simp [peirceWindow]

/-- The finite windowed family is defined by the actual Weyl action. -/
def windowAtoms (k : Fin 4) : Matrix (Fin 2) (Fin 2) B :=
  weylFamily k * peirceWindow

omit [StarRing B] in
/-- The four windowed atoms have at most two different values. -/
theorem windowAtoms_eq :
    windowAtoms (B := B) =
      ![peirceWindow, peirceWindow, Matrix.single 1 0 1, Matrix.single 1 0 1] := by
  funext k
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [windowAtoms, weylFamily, peirceWindow, I_mat, Gamma_mat, J_mat,
      K_mat, Matrix.single, Matrix.mul_apply]

/-- The unnormalized four-conjugation twirl is a scalar matrix. The
coefficient order is valid without commutativity of `B`. -/
theorem weyl_twirl (M : Matrix (Fin 2) (Fin 2) B) :
    krausChannel weylFamily M = Matrix.scalar (Fin 2) (2 * (M 0 0 + M 1 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [krausChannel, weylFamily, I_mat, Gamma_mat, J_mat, K_mat,
      Matrix.mul_apply, Matrix.star_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.scalar_apply] <;> noncomm_ring

/-- The unnormalized twirl is four times idempotent, rather than an
idempotent map in characteristic zero. -/
theorem weyl_twirl_twice (M : Matrix (Fin 2) (Fin 2) B) :
    krausChannel weylFamily (krausChannel weylFamily M) =
      (4 : ℕ) • krausChannel weylFamily M := by
  simp only [weyl_twirl]
  ext i j
  change _ = (4 : ℕ) • (Matrix.scalar (Fin 2) (2 * (M 0 0 + M 1 1)) i j)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, nsmul_eq_mul] <;> noncomm_ring

/-- Evaluating at the identity witnesses that the unnormalized twirl is
not idempotent over a characteristic-zero coefficient ring. -/
theorem weyl_twirl_twice_one_ne [CharZero B] :
    krausChannel weylFamily
        (krausChannel (weylFamily (B := B)) 1) ≠
      krausChannel (weylFamily (B := B)) 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  norm_num [weyl_twirl, Matrix.scalar_apply, Matrix.diagonal_apply] at h00

/-- A genuine finite mask acts through the general operator-valued
multiplier, with zero/one matrix coefficients. -/
def maskedFrame (s : Finset (Fin 4)) : Matrix (Fin 2) (Fin 2) B :=
  multiplier windowAtoms (fun k => if k ∈ s then 1 else 0)

/-- The mask implementation is exactly the partial frame sum. -/
theorem maskedFrame_eq_sum (s : Finset (Fin 4)) :
    maskedFrame (B := B) s = ∑ k ∈ s, windowAtoms k * star (windowAtoms k) :=
  multiplier_indicator windowAtoms s

/-- The balanced choice contains one atom of each matrix-unit type. -/
def balancedSelection : Finset (Fin 4) := {0, 2}

/-- The parallel choice contains the two copies of the first matrix unit. -/
def parallelSelection : Finset (Fin 4) := {0, 1}

@[simp] theorem card_balancedSelection : balancedSelection.card = 2 := by
  simp [balancedSelection]

@[simp] theorem card_parallelSelection : parallelSelection.card = 2 := by
  simp [parallelSelection]

/-- The complete four-atom window has frame operator `2I`. -/
theorem full_mask :
    maskedFrame (B := B) Finset.univ = 1 + 1 := by
  rw [maskedFrame_eq_sum, windowAtoms_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceWindow, Matrix.single, Matrix.mul_apply, Matrix.star_apply,
      Fin.sum_univ_succ]

/-- A balanced half of the four-atom family is Parseval. -/
theorem balanced_mask :
    maskedFrame (B := B) balancedSelection = 1 := by
  rw [maskedFrame_eq_sum, windowAtoms_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedSelection, peirceWindow, Matrix.single, Matrix.mul_apply,
      Matrix.star_apply]

/-- The same number of parallel atoms gives twice the Peirce projection. -/
theorem parallel_mask :
    maskedFrame (B := B) parallelSelection = peirceWindow + peirceWindow := by
  rw [maskedFrame_eq_sum, windowAtoms_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parallelSelection, peirceWindow, Matrix.single, Matrix.mul_apply,
      Matrix.star_apply]

/-- A singleton mask retains the Peirce projection itself. -/
theorem singleton_mask :
    maskedFrame (B := B) {0} = peirceWindow := by
  rw [maskedFrame_eq_sum, windowAtoms_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceWindow, Matrix.single, Matrix.mul_apply, Matrix.star_apply]

/-- The parallel half cannot be Parseval in a nontrivial coefficient ring. -/
theorem parallel_mask_ne_one [Nontrivial B] :
    maskedFrame (B := B) parallelSelection ≠ 1 := by
  rw [parallel_mask]
  intro h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 1 1) h
  simp [peirceWindow, Matrix.single] at h11

/-- Equal cardinality is insufficient to determine a finite masked frame
operator. This explicit witness places no metric meaning on a finite mask. -/
theorem equal_cardinality_masks_need_not_agree [Nontrivial B] :
    ∃ s t : Finset (Fin 4), s.card = t.card ∧
      maskedFrame (B := B) s ≠ maskedFrame t := by
  refine ⟨balancedSelection, parallelSelection, by simp, ?_⟩
  rw [balanced_mask]
  exact Ne.symm parallel_mask_ne_one

end InfoGeometry.Clifford.WeylFrameMasks
