/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BinaryCarry
import InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

/-!
# An integral Peirce factorization of the existing eighth-cyclotomic companion

The four matrices below exhibit the existing `phi8Companion` as a binary carry.
The carried element is the existing Peirce expression `genJ` for a first cut
and flip, not a new scalar phase or an independently defined matrix root.

All matrices have entries in `ℤ`. The general ring theorems supply the exact
order, the two inverse products and composite-reflection conjugation. In this
particular representation the explicit inverse equals the transpose. The
first grading alone does not invert the companion, and the companion does not
commute with the second cut.
-/

namespace InfoGeometry.Canonical.RealCarryMatrix

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

/-- The second bit selects the even coordinate indices. -/
def secondCut : M4 :=
  !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

/-- An integral involution exchanging the two second-bit corners. -/
def secondFlip : M4 :=
  !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0]

/-- The first bit selects the first and last coordinates. -/
def firstCut : M4 :=
  !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]

/-- The normalized off-diagonal bridge for the first cut. -/
def firstFlip : M4 :=
  !![0, 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The first bit's oriented Peirce bridge. -/
def firstComplex : M4 := genJ firstCut firstFlip firstFlip

/-- The first bit's Peirce grading. -/
def firstGrading : M4 := invS firstCut

theorem firstCut_idempotent : firstCut * firstCut = firstCut := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem firstFlip_involution : firstFlip * firstFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The bridge is already entirely off diagonal for the first cut. -/
theorem firstPhi_eq : genPhi firstCut firstFlip firstFlip = firstFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The square-negative law comes from normalized Peirce geometry. -/
theorem firstComplex_square : firstComplex * firstComplex = -1 := by
  exact genJ_sq_of_genPhi_sq firstCut_idempotent firstFlip firstFlip
    (by simpa only [firstPhi_eq] using firstFlip_involution)

/-- The carried Peirce element is the square of the pre-existing companion. -/
theorem firstComplex_eq_companion_sq : firstComplex = phi8Companion ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem secondCut_idempotent : secondCut * secondCut = secondCut := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem secondFlip_involution : secondFlip * secondFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem secondFlip_swaps_cut : secondFlip * secondCut = (1 - secondCut) * secondFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem firstComplex_commute_secondCut : Commute firstComplex secondCut := by
  change firstComplex * secondCut = secondCut * firstComplex
  rw [firstComplex_eq_companion_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem firstComplex_commute_secondFlip : Commute firstComplex secondFlip := by
  change firstComplex * secondFlip = secondFlip * firstComplex
  rw [firstComplex_eq_companion_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The abstract carry expression factors the existing companion exactly. -/
theorem binaryCarry_eq_phi8Companion :
    binaryCarry secondCut secondFlip firstComplex = phi8Companion := by
  rw [firstComplex_eq_companion_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- This integral model's explicit inverse is the ordinary transpose. -/
theorem binaryCarryInverse_eq_transpose :
    binaryCarryInverse secondCut secondFlip firstComplex = phi8Companion.transpose := by
  rw [firstComplex_eq_companion_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Exact order eight follows from the general carry theorem in characteristic zero. -/
theorem phi8Companion_orderOf_eight : orderOf phi8Companion = 8 := by
  simpa only [binaryCarry_eq_phi8Companion] using
    binaryCarry_orderOf_eight secondCut_idempotent secondFlip_involution
      secondFlip_swaps_cut firstComplex_commute_secondCut firstComplex_commute_secondFlip
      firstComplex_square (by decide : (-1 : M4) ≠ 1)

theorem phi8Companion_mul_transpose : phi8Companion * phi8Companion.transpose = 1 := by
  simpa only [binaryCarry_eq_phi8Companion, binaryCarryInverse_eq_transpose] using
    binaryCarry_mul_inverse secondCut_idempotent secondFlip_involution
      secondFlip_swaps_cut firstComplex_commute_secondCut firstComplex_commute_secondFlip
      firstComplex_square

theorem phi8Companion_transpose_mul : phi8Companion.transpose * phi8Companion = 1 := by
  simpa only [binaryCarry_eq_phi8Companion, binaryCarryInverse_eq_transpose] using
    binaryCarry_inverse_mul secondCut_idempotent secondFlip_involution
      secondFlip_swaps_cut firstComplex_commute_secondCut firstComplex_commute_secondFlip
      firstComplex_square

theorem firstGrading_involution : firstGrading * firstGrading = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem firstGrading_commute_secondCut : Commute firstGrading secondCut := by
  change firstGrading * secondCut = secondCut * firstGrading
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem firstGrading_commute_secondFlip : Commute firstGrading secondFlip := by
  change firstGrading * secondFlip = secondFlip * firstGrading
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The first grading reverses the carried complex structure's sign. -/
theorem firstGrading_anticommutes_complex :
    firstGrading * firstComplex = -(firstComplex * firstGrading) := by
  change invS firstCut * genJ firstCut firstFlip firstFlip =
    -(genJ firstCut firstFlip firstFlip * invS firstCut)
  simp only [invS_mul_genJ firstCut_idempotent, genJ_mul_invS firstCut_idempotent, neg_neg]

/-- The two commuting involutions form the required inverse reflection. -/
def carryReflection : M4 := firstGrading * secondFlip

theorem carryReflection_involution : carryReflection * carryReflection = 1 := by
  exact carryReflection_sq firstGrading_involution secondFlip_involution
    firstGrading_commute_secondFlip

/-- Composite reflection implements inverse conjugation for the integral companion. -/
theorem carryReflection_conjugates_companion_to_transpose :
    carryReflection * phi8Companion * carryReflection = phi8Companion.transpose := by
  simpa only [carryReflection, binaryCarry_eq_phi8Companion, binaryCarryInverse_eq_transpose] using
    carryReflection_conjugates firstGrading_involution secondFlip_involution secondFlip_swaps_cut
      firstGrading_commute_secondCut firstGrading_commute_secondFlip
      firstGrading_anticommutes_complex firstComplex_commute_secondFlip

/-- The first grading alone does not implement inverse conjugation. -/
theorem firstGrading_does_not_invert_companion :
    firstGrading * phi8Companion * firstGrading ≠ phi8Companion.transpose := by
  intro h
  have hneq : (firstGrading * phi8Companion * firstGrading) 0 3 ≠
      phi8Companion.transpose 0 3 := by decide
  exact hneq (congrArg (fun m : M4 => m 0 3) h)

/-- An internal cyclotomic operator need not be central in its matrix algebra. -/
theorem phi8Companion_not_commute_secondCut : ¬ Commute phi8Companion secondCut := by
  intro h
  have hneq : (phi8Companion * secondCut) 0 3 ≠ (secondCut * phi8Companion) 0 3 := by decide
  exact hneq (congrArg (fun m : M4 => m 0 3) h.eq)

end InfoGeometry.Canonical.RealCarryMatrix
