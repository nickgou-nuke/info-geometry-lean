import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import proofs.CartanDecomposition

open Matrix

abbrev Matrix4x4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ

noncomputable def kreinDoubling (M : Patch2x2) : Matrix4x4 :=
  fromBlocks (symmPart M) (skewPart M) (skewPart M) (symmPart M)

theorem symmPart_add (A B : Patch2x2) : symmPart (A + B) = symmPart A + symmPart B := by
  ext i j; dsimp [symmPart]; ring

theorem skewPart_add (A B : Patch2x2) : skewPart (A + B) = skewPart A + skewPart B := by
  ext i j; dsimp [skewPart]; ring

theorem kreinDoubling_add (A B : Patch2x2) :
    kreinDoubling (A + B) = kreinDoubling A + kreinDoubling B := by
  dsimp [kreinDoubling]
  rw [symmPart_add, skewPart_add]
  rw [← fromBlocks_add]
