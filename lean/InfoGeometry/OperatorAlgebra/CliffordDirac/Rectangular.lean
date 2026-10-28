/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CliffordDirac.Grading
import InfoGeometry.Krein.FiniteDiracGramSquare

/-!
# A Hermitian charge pair on an arbitrary rectangular matrix

The first charge and its two Gram blocks are the existing finite Dirac owner.
This module supplies the actual grading and the complex second charge. The
rectangular input is unrestricted. The Gram operators act on their respective
summands, and even for square input they need not coincide.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

open Matrix
open scoped ComplexOrder MatrixOrder
open InfoGeometry.Krein.FiniteDiracGramSquare

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The grading on the two actual summands of the rectangular Dirac space. -/
def rectangularGrading : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix n n ℂ)

theorem rectangularGrading_sq :
    (rectangularGrading : Matrix (m ⊕ n) (m ⊕ n) ℂ) * rectangularGrading = 1 := by
  simp [rectangularGrading, fromBlocks_multiply]

omit [Fintype m] [Fintype n] in
theorem rectangularGrading_selfAdjoint :
    IsSelfAdjoint (rectangularGrading : Matrix (m ⊕ n) (m ⊕ n) ℂ) := by
  change (rectangularGrading : Matrix (m ⊕ n) (m ⊕ n) ℂ)ᴴ = rectangularGrading
  simp [rectangularGrading, fromBlocks_conjTranspose]

theorem rectangularGrading_mul_dirac (T : Matrix m n ℂ) :
    rectangularGrading * dirac T = qPlus T - qMinus T := by
  rw [rectangularGrading, dirac, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [qPlus, qMinus, fromBlocks]

theorem rectangularGrading_odd (T : Matrix m n ℂ) :
    rectangularGrading * dirac T + dirac T * rectangularGrading = 0 := by
  simp only [rectangularGrading, dirac, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

/-- The equal-square second charge, with its complex sign fixed explicitly. -/
def secondBlockCharge (T : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  chiralMate rectangularGrading (dirac T)

theorem secondBlockCharge_eq (T : Matrix m n ℂ) :
    secondBlockCharge T = Complex.I • (qPlus T - qMinus T) := by
  rw [secondBlockCharge, chiralMate, rectangularGrading_mul_dirac]

theorem secondBlockCharge_selfAdjoint (T : Matrix m n ℂ) :
    IsSelfAdjoint (secondBlockCharge T) :=
  chiralMate_selfAdjoint rectangularGrading_selfAdjoint
    (dirac_isHermitian T) (rectangularGrading_odd T)

theorem secondBlockCharge_sq (T : Matrix m n ℂ) :
    secondBlockCharge T * secondBlockCharge T = dirac T * dirac T :=
  chiralMate_sq rectangularGrading_sq (rectangularGrading_odd T)

theorem secondBlockCharge_sq_eq_grams (T : Matrix m n ℂ) :
    secondBlockCharge T * secondBlockCharge T =
      fromBlocks (leftGram T) 0 0 (rightGram T) := by
  rw [secondBlockCharge_sq, dirac_sq]

theorem block_charges_anticommute (T : Matrix m n ℂ) :
    dirac T * secondBlockCharge T + secondBlockCharge T * dirac T = 0 :=
  chiralMate_anticommute (rectangularGrading_odd T)

theorem secondBlockCharge_odd (T : Matrix m n ℂ) :
    rectangularGrading * secondBlockCharge T + secondBlockCharge T * rectangularGrading = 0 :=
  chiralMate_odd (rectangularGrading_odd T)

theorem secondBlockCharge_commute_hamiltonian (T : Matrix m n ℂ) :
    Commute (secondBlockCharge T) (dirac T * dirac T) :=
  chiralMate_commute_square rectangularGrading_sq (rectangularGrading_odd T)

omit [DecidableEq m] [DecidableEq n] in
theorem block_hamiltonian_posSemidef (T : Matrix m n ℂ) :
    (dirac T * dirac T).PosSemidef := by
  classical
  simpa only [(dirac_isHermitian T).eq] using posSemidef_conjTranspose_mul_self (dirac T)

omit [DecidableEq m] [DecidableEq n] in
/-- The two Gram operators are intertwined by the rectangular input itself. -/
theorem gram_intertwining (T : Matrix m n ℂ) :
    leftGram T * T = T * rightGram T := Matrix.mul_assoc _ _ _

omit [DecidableEq m] [DecidableEq n] in
/-- The kernel condition retains both summands and the actual adjoint. -/
theorem dirac_mulVec_eq_zero_iff (T : Matrix m n ℂ) (u : m → ℂ) (v : n → ℂ) :
    dirac T *ᵥ Sum.elim u v = 0 ↔ T *ᵥ v = 0 ∧ Tᴴ *ᵥ u = 0 := by
  rw [dirac, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, add_zero]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext j
      exact congrFun h (Sum.inr j)
  · rintro ⟨hv, hu⟩
    funext i
    cases i with
    | inl i => exact congrFun hv i
    | inr j => exact congrFun hu j

end InfoGeometry.OperatorAlgebra.CliffordDirac
