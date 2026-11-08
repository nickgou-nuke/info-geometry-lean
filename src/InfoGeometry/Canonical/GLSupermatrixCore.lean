import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite supermatrix core

The native associative carrier for finite `(m|n)` supermatrices.  This file
keeps only the block and supertrace facts that are independent of any choice
of Grassmann algebra or analytic supergroup.
-/

namespace InfoGeometry.Canonical.GLSupermatrixCore

inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

abbrev SuperMatrix (m n : ℕ) (R : Type*) :=
  Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R

variable {m n : ℕ} {R : Type*}

def blockA (M : SuperMatrix m n R) : Matrix (Fin m) (Fin m) R :=
  fun i j => M (Sum.inl i) (Sum.inl j)

def blockD (M : SuperMatrix m n R) : Matrix (Fin n) (Fin n) R :=
  fun i j => M (Sum.inr i) (Sum.inr j)

variable [CommRing R]

def evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : SuperMatrix m n R :=
  Matrix.fromBlocks A 0 0 D

def oddMatrix (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) : SuperMatrix m n R :=
  Matrix.fromBlocks 0 B C 0

@[simp] theorem blockA_evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : blockA (evenMatrix A D) = A := by
  ext i j
  rfl

@[simp] theorem blockD_evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : blockD (evenMatrix A D) = D := by
  ext i j
  rfl

@[simp] theorem blockA_oddMatrix [Nontrivial R]
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    blockA (oddMatrix B C) = 0 := by
  ext i j
  rfl

@[simp] theorem blockD_oddMatrix [Nontrivial R]
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    blockD (oddMatrix B C) = 0 := by
  ext i j
  rfl

def supertrace (M : SuperMatrix m n R) : R :=
  Matrix.trace (blockA M) - Matrix.trace (blockD M)

@[simp] theorem supertrace_evenMatrix
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    supertrace (evenMatrix A D) = Matrix.trace A - Matrix.trace D := by
  simp [supertrace]

@[simp] theorem supertrace_oddMatrix [Nontrivial R]
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    supertrace (oddMatrix B C) = 0 := by
  unfold supertrace
  rw [blockA_oddMatrix, blockD_oddMatrix]
  change (∑ i : Fin m, (0 : R)) - ∑ i : Fin n, (0 : R) = 0
  have hm : (∑ i : Fin m, (0 : R)) = 0 := by
    simpa using (mul_zero (m : R))
  have hn : (∑ i : Fin n, (0 : R)) = 0 := by
    simpa using (mul_zero (n : R))
  rw [hm, hn]
  change (0 : R) - 0 = 0
  exact sub_self (0 : R)

end InfoGeometry.Canonical.GLSupermatrixCore
