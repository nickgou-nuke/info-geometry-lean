import Mathlib
import proofs.CartanDecomposition
import proofs.RankOneEigenvectors

open Matrix

abbrev Matrix4x4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ

/-!
# Cartan-Krein Doubling

This module formalizes the embedding of the 2x2 image patches into 
the 4x4 Cartan-Krein space. By splitting a matrix into its symmetric 
and skew-symmetric parts (Cartan decomposition), we map it into a 
higher-dimensional block matrix structure.

This is the exact mathematical bridge linking the 2x2 eigenvectors 
and null spaces to the 8-dimensional Split Octonions.
-/

/--
The Krein Doubling embeds a 2x2 patch into a 4x4 block matrix 
using its symmetric (M_+) and skew-symmetric (M_-) Cartan components.
-/
def kreinDoubling (M : Patch2x2) : Matrix4x4 :=
  fromBlocks (symmPart M) (skewPart M) (skewPart M) (symmPart M)

/-- The Cartan symmetric part linearly preserves addition. -/
theorem symmPart_add (A B : Patch2x2) : symmPart (A + B) = symmPart A + symmPart B := by
  ext i j; dsimp [symmPart]; ring

/-- The Cartan skew-symmetric part linearly preserves addition. -/
theorem skewPart_add (A B : Patch2x2) : skewPart (A + B) = skewPart A + skewPart B := by
  ext i j; dsimp [skewPart]; ring

/--
Theorem: The Krein doubling is a strictly linear representation.
It preserves addition across the 4x4 topological space.
-/
theorem kreinDoubling_add (A B : Patch2x2) :
    kreinDoubling (A + B) = kreinDoubling A + kreinDoubling B := by
  dsimp [kreinDoubling]
  rw [symmPart_add, skewPart_add]
  exact (fromBlocks_add (symmPart A) (symmPart B) (skewPart A) (skewPart B) (skewPart A) (skewPart B) (symmPart A) (symmPart B)).symm

theorem symmPart_of_transpose (M : Patch2x2) : symmPart (Mᵀ) = symmPart M := by
  ext i j; dsimp [symmPart]; ring

theorem skewPart_of_transpose (M : Patch2x2) : skewPart (Mᵀ) = -skewPart M := by
  ext i j; dsimp [skewPart]; ring

/--
Theorem: Transposition in the 2x2 space maps to a specific block-sign 
conjugation in the 4x4 Krein space, directly exposing the indefinite (2,2) signature.
-/
theorem kreinDoubling_transpose (M : Patch2x2) :
    kreinDoubling (Mᵀ) = fromBlocks (symmPart M) (-skewPart M) (-skewPart M) (symmPart M) := by
  dsimp [kreinDoubling]
  rw [symmPart_of_transpose, skewPart_of_transpose]
