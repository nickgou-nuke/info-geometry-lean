/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Symmetric Positive Definite Matrices

Canonical finite-dimensional SPD model.
-/

namespace InfoGeometry.Jordan

open Matrix

/-- Real symmetric positive-definite matrices. -/
structure SPD (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℝ
  symm : Matrix.IsSymm mat
  pos : Matrix.PosDef mat

/-- The identity matrix is a canonical SPD covariance in every finite dimension. -/
def SPD.identity (n : ℕ) : SPD n where
  mat := 1
  symm := Matrix.isSymm_one
  pos := Matrix.PosDef.one

@[simp]
theorem SPD.identity_mat (n : ℕ) :
    (SPD.identity n).mat = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

instance (n : ℕ) : Inhabited (SPD n) := ⟨SPD.identity n⟩

instance {n : ℕ} : Coe (SPD n) (Matrix (Fin n) (Fin n) ℝ) where
  coe A := A.mat

@[simp]
lemma SPD.transpose_eq_self {n : ℕ} (A : SPD n) :
    Matrix.transpose A.mat = A.mat := by
  simpa [Matrix.IsSymm] using A.symm

lemma SPD.posDef {n : ℕ} (A : SPD n) : A.mat.PosDef :=
  A.pos

variable {n : ℕ}

/-- Positive scalar multiplication preserves the existing SPD carrier. -/
noncomputable def SPD.rescale (X : SPD n) (r : ℝ) (hr : 0 < r) : SPD n where
  mat := r • X.mat
  symm := by
    change (r • X.mat)ᵀ = r • X.mat
    rw [Matrix.transpose_smul, X.transpose_eq_self]
  pos := X.pos.smul hr

@[simp]
theorem SPD.rescale_mat (X : SPD n) (r : ℝ) (hr : 0 < r) :
    (X.rescale r hr).mat = r • X.mat := rfl

end InfoGeometry.Jordan
