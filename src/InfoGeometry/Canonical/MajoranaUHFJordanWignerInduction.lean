/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Basic.Real.Basic

/-!
# Finite Jordan–Wigner successor step

For a finite stage matrix carrier, this file proves the block-matrix CAR and
parity identities for adjoining one mode using the previous stage parity
involution. It is an algebraic successor lemma; it does not identify this
generic block embedding with the repository's concrete Cuntz `MatrixStage`
bonding map or assert a KMS eigen-action.
-/

noncomputable section

namespace InfoGeometry.Canonical.MajoranaUHFJordanWignerInduction

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Odd-odd superbracket, i.e. the CAR anticommutator. -/
def oddSuperBracket (A B : Matrix m m ℝ) : Matrix m m ℝ := A * B + B * A

/-- Embed an old-stage operator as `A ⊗ I₂`, in block form. -/
def oldMode (A : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks A 0 0 A

/-- Creation operator for the new mode, with the old parity string. -/
def newCreate (Γ : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks 0 0 Γ 0

/-- Annihilation operator for the new mode. -/
def newAnnihilate (Γ : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks 0 Γ 0 0

/-- Successor parity operator. -/
def nextParity (Γ : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks Γ 0 0 (-Γ)

/-- The block embedding preserves odd-odd superbrackets, so all old-stage CAR
relations survive adjoining the new mode. -/
theorem oldMode_oddSuperBracket (A B : Matrix m m ℝ) :
    oddSuperBracket (oldMode A) (oldMode B) =
      oldMode (oddSuperBracket A B) := by
  unfold oddSuperBracket oldMode
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  simpa using Matrix.fromBlocks_add (A * B) 0 0 (A * B) (B * A) 0 0 (B * A)

/-- An old-stage CAR scalar identity remains the same scalar identity after
the block embedding. -/
theorem oldMode_preserves_car_metric
    (A B : Matrix m m ℝ) (c : ℝ)
    (hCAR : oddSuperBracket A B = c • (1 : Matrix m m ℝ)) :
    oddSuperBracket (oldMode A) (oldMode B) =
      c • (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by
  rw [oldMode_oddSuperBracket, hCAR]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [oldMode, Matrix.one_apply]

theorem nextParity_sq (Γ : Matrix m m ℝ) (hΓ : Γ * Γ = 1) :
    nextParity Γ * nextParity Γ = (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by
  unfold nextParity
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [hΓ, Matrix.one_apply]

theorem newCreate_sq (Γ : Matrix m m ℝ) :
    newCreate Γ * newCreate Γ = 0 := by
  unfold newCreate
  rw [Matrix.fromBlocks_multiply]
  simp

theorem newAnnihilate_sq (Γ : Matrix m m ℝ) :
    newAnnihilate Γ * newAnnihilate Γ = 0 := by
  unfold newAnnihilate
  rw [Matrix.fromBlocks_multiply]
  simp

theorem newMode_car (Γ : Matrix m m ℝ) (hΓ : Γ * Γ = 1) :
    oddSuperBracket (newCreate Γ) (newAnnihilate Γ) =
      (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by
  unfold oddSuperBracket newCreate newAnnihilate
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [hΓ, Matrix.one_apply]

theorem old_newCreate_anticomm
    (A Γ : Matrix m m ℝ) (hOdd : oddSuperBracket A Γ = 0) :
    oddSuperBracket (oldMode A) (newCreate Γ) = 0 := by
  unfold oddSuperBracket oldMode newCreate
  change A * Γ + Γ * A = 0 at hOdd
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp
  · simp
  · have hEntry := congrArg (fun M : Matrix m m ℝ => M i j) hOdd
    simpa using hEntry
  · simp

theorem old_newAnnihilate_anticomm
    (A Γ : Matrix m m ℝ) (hOdd : oddSuperBracket A Γ = 0) :
    oddSuperBracket (oldMode A) (newAnnihilate Γ) = 0 := by
  unfold oddSuperBracket oldMode newAnnihilate
  change A * Γ + Γ * A = 0 at hOdd
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp
  · have hEntry := congrArg (fun M : Matrix m m ℝ => M i j) hOdd
    simpa using hEntry
  · simp
  · simp

theorem oldMode_nextParity_anticomm
    (A Γ : Matrix m m ℝ) (hOdd : oddSuperBracket A Γ = 0) :
    oddSuperBracket (oldMode A) (nextParity Γ) = 0 := by
  unfold oddSuperBracket oldMode nextParity
  change A * Γ + Γ * A = 0 at hOdd
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hEntry := congrArg (fun M : Matrix m m ℝ => M i j) hOdd
    simpa using hEntry
  · simp
  · simp
  · have hEntry := congrArg (fun M : Matrix m m ℝ => M i j) hOdd
    simpa [add_comm] using congrArg Neg.neg hEntry

theorem newCreate_nextParity_anticomm
    (Γ : Matrix m m ℝ) :
    oddSuperBracket (newCreate Γ) (nextParity Γ) = 0 := by
  unfold oddSuperBracket newCreate nextParity
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [add_comm]

/-- The new annihilation block is odd for the successor parity operator. -/
theorem newAnnihilate_nextParity_anticomm
    (Γ : Matrix m m ℝ) :
    oddSuperBracket (newAnnihilate Γ) (nextParity Γ) = 0 := by
  unfold oddSuperBracket newAnnihilate nextParity
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [add_comm]

end InfoGeometry.Canonical.MajoranaUHFJordanWignerInduction
