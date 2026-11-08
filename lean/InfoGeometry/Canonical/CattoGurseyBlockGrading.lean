/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GLSupermatrixGradedLie
import InfoGeometry.Core.PeirceGrading

/-!
# Native block realization of the corrected 6|21 matrix sector

The associative carrier is Mathlib's matrix algebra on `Fin m ⊕ Fin n`.
This file identifies its existing homogeneous block spaces with the actual
Peirce direct sum. The imported owner supplies the superbracket, graded closure,
super-Jacobi, and supertrace laws. This is `gl(m|n)`, not a claim of a unitary
real form, and is not a multiplication-preserving realization of octonions.
-/

namespace InfoGeometry.Canonical.CattoGurseyBlockGrading
open GLSupermatrixGradedLie
open InfoGeometry.Core.PeirceGrading

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- First-block support; `m=6,n=21` is the proposed quark-sector size. -/
def firstSupport : SuperMatrix m n R := evenMatrix 1 0

/-- Second-block support. -/
def secondSupport : SuperMatrix m n R := evenMatrix 0 1

theorem firstSupport_idempotent : IsIdempotentElem (firstSupport : SuperMatrix m n R) := by
  change evenMatrix 1 0 * evenMatrix 1 0 = evenMatrix 1 0
  rw [GLSupermatrixGradedLie.even_mul_even]
  simp

theorem secondSupport_eq_complement :
    (secondSupport : SuperMatrix m n R) = 1 - firstSupport := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [firstSupport, secondSupport, evenMatrix, Matrix.one_apply]

/-- Exact four block compressions on arbitrary rectangular block data. -/
theorem corner_blocks (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    firstSupport * Matrix.fromBlocks A B C D * firstSupport = evenMatrix A 0 ∧
    secondSupport * Matrix.fromBlocks A B C D * secondSupport = evenMatrix 0 D ∧
    firstSupport * Matrix.fromBlocks A B C D * secondSupport = oddMatrix B 0 ∧
    secondSupport * Matrix.fromBlocks A B C D * firstSupport = oddMatrix 0 C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [firstSupport, secondSupport, evenMatrix, oddMatrix, Matrix.fromBlocks_multiply]

/-- Peirce's linear projections coincide with the existing native block split. -/
theorem peirce_components (H : SuperMatrix m n R) :
    even firstSupport H = evenMatrix (blockA H) (blockD H) ∧
    odd firstSupport H = oddMatrix (blockB H) (blockC H) := by
  have hrep : Matrix.fromBlocks (blockA H) (blockB H) (blockC H) (blockD H) = H :=
    Matrix.fromBlocks_toBlocks H
  have hc := corner_blocks (blockA H) (blockB H) (blockC H) (blockD H)
  rw [hrep] at hc
  constructor
  · rw [even_apply, ← secondSupport_eq_complement, hc.1, hc.2.1]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [evenMatrix]
  · rw [odd_apply, ← secondSupport_eq_complement, hc.2.2.1, hc.2.2.2]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [oddMatrix]

/-- The block-even predicate is the range of the native Peirce projection. -/
theorem homogeneous_even_iff (H : SuperMatrix m n R) :
    IsHomogeneous .even H ↔ H ∈ LinearMap.range (even firstSupport) := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (even_idempotent firstSupport_idempotent)]
  constructor
  · rintro ⟨A,D,rfl⟩
    rw [(peirce_components _).1]
    simp
  · intro h
    exact ⟨blockA H, blockD H, h.symm.trans (peirce_components H).1⟩

/-- The block-odd predicate is the complementary native Peirce range. -/
theorem homogeneous_odd_iff (H : SuperMatrix m n R) :
    IsHomogeneous .odd H ↔ H ∈ LinearMap.range (odd firstSupport) := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent firstSupport_idempotent)]
  constructor
  · rintro ⟨B,C,rfl⟩
    rw [(peirce_components _).2]
    rfl
  · intro h
    exact ⟨blockB H, blockC H, h.symm.trans (peirce_components H).2⟩

/-- Each directed odd block squares to zero. The sum need not do so. -/
theorem directed_blocks_square_zero (H : SuperMatrix m n R) :
    (oddMatrix (blockB H) 0 : SuperMatrix m n R)^2 = 0 ∧
    (oddMatrix 0 (blockC H) : SuperMatrix m n R)^2 = 0 := by
  constructor <;> rw [sq, GLSupermatrixGradedLie.odd_mul_odd] <;>
    ext i j <;> rcases i with i | i <;> rcases j with j | j <;> simp [evenMatrix]

/-- In the actual 6|21 carrier the identity has supertrace -15.
Nonvanishing requires that 15 be nonzero in the coefficient ring.
A special-unitary interpretation requires additional, separate structure. -/
theorem supertrace_identity_6_21 : supertrace (1 : SuperMatrix 6 21 R) = -15 := by
  have h : (1 : SuperMatrix 6 21 R) = evenMatrix 1 1 := Matrix.fromBlocks_one.symm
  rw [h, supertrace_evenMatrix]
  simp [Matrix.trace_one]
  ring

end InfoGeometry.Canonical.CattoGurseyBlockGrading
