import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# InfoGeometry.Clifford.Cl44QuaternionSplit

Conservative owner surface for a Bektaş-style block dictionary:
represent an abstract carrier by a quaternion pair `(q₁, q₂)` and map it to a
`2 × 2` quaternion block matrix.

This file does **not** identify Zorn/split-octonion multiplication with
ordinary associative matrix multiplication. It only records the coordinate
roundtrip interface and the explicit block map in an associative envelope.
-/

namespace InfoGeometry.Clifford.Cl44QuaternionSplit

open scoped Matrix

/-- Explicit `2×2` quaternion block used in the Bektaş dictionary. -/
def bektasBlock (q₁ q₂ : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) :=
  !![q₁, q₂;
    star q₂, star q₁]

@[simp] theorem bektasBlock_00 (q₁ q₂ : Quaternion ℝ) :
    bektasBlock q₁ q₂ 0 0 = q₁ := by
  simp [bektasBlock]

@[simp] theorem bektasBlock_01 (q₁ q₂ : Quaternion ℝ) :
    bektasBlock q₁ q₂ 0 1 = q₂ := by
  simp [bektasBlock]

@[simp] theorem bektasBlock_10 (q₁ q₂ : Quaternion ℝ) :
    bektasBlock q₁ q₂ 1 0 = star q₂ := by
  simp [bektasBlock]

@[simp] theorem bektasBlock_11 (q₁ q₂ : Quaternion ℝ) :
    bektasBlock q₁ q₂ 1 1 = star q₁ := by
  simp [bektasBlock]

/-- The Bektaş block dictionary remembers the quaternion pair uniquely. -/
theorem bektasBlock_injective :
    Function.Injective (fun p : Quaternion ℝ × Quaternion ℝ => bektasBlock p.1 p.2) := by
  intro p q h
  cases p with
  | mk q₁ q₂ =>
      cases q with
      | mk r₁ r₂ =>
          have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) => M 0 0) h
          have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) => M 0 1) h
          simp [bektasBlock] at h00 h01
          cases h00
          cases h01
          rfl

/--
Minimal interface for a split-octonion-like carrier with quaternion-pair
coordinates.
-/
structure BektasSplitDatum where
  Os : Type
  toPair : Os → Quaternion ℝ × Quaternion ℝ
  ofPair : Quaternion ℝ × Quaternion ℝ → Os
  left_inv : ∀ x : Os, ofPair (toPair x) = x
  right_inv : ∀ p : Quaternion ℝ × Quaternion ℝ, toPair (ofPair p) = p

namespace BektasSplitDatum

/-- Block realization induced by a `BektasSplitDatum`. -/
def toBlock (D : BektasSplitDatum) (x : D.Os) : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) :=
  bektasBlock (D.toPair x).1 (D.toPair x).2

/-- The block realization of a paired element is the expected Bektaş block. -/
theorem toBlock_ofPair (D : BektasSplitDatum) (p : Quaternion ℝ × Quaternion ℝ) :
    D.toBlock (D.ofPair p) = bektasBlock p.1 p.2 := by
  simpa [BektasSplitDatum.toBlock] using congrArg
    (fun p' : Quaternion ℝ × Quaternion ℝ => bektasBlock p'.1 p'.2)
    (D.right_inv p)

/-- The block realization is injective when the pair dictionary is a round-trip. -/
theorem toBlock_injective (D : BektasSplitDatum) : Function.Injective D.toBlock := by
  intro x y h
  have hp : D.toPair x = D.toPair y := by
    apply bektasBlock_injective
    simpa [BektasSplitDatum.toBlock] using h
  calc
    x = D.ofPair (D.toPair x) := (D.left_inv x).symm
    _ = D.ofPair (D.toPair y) := by rw [hp]
    _ = y := D.left_inv y

/-- Coordinate-level left inverse, re-exported as theorem surface. -/
theorem ofPair_toPair (D : BektasSplitDatum) (x : D.Os) :
    D.ofPair (D.toPair x) = x :=
  D.left_inv x

/-- Coordinate-level right inverse, re-exported as theorem surface. -/
theorem toPair_ofPair (D : BektasSplitDatum) (p : Quaternion ℝ × Quaternion ℝ) :
    D.toPair (D.ofPair p) = p :=
  D.right_inv p

end BektasSplitDatum

/-- Associativity of the ambient quaternion `2×2` matrix multiplication. -/
theorem bektasBlock_mul_assoc
    (A B C : Matrix (Fin 2) (Fin 2) (Quaternion ℝ)) :
    (A * B) * C = A * (B * C) := by
  simpa using Matrix.mul_assoc A B C

end InfoGeometry.Clifford.Cl44QuaternionSplit
