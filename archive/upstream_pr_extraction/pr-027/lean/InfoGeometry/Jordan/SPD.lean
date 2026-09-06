import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Symmetric Positive Definite Matrices

Canonical finite-dimensional SPD model.
-/

namespace InfoGeometry.Jordan

/-- Real symmetric positive-definite matrices. -/
structure SPD (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℝ
  symm : Matrix.IsSymm mat
  pos : Matrix.PosDef mat

instance {n : ℕ} : Coe (SPD n) (Matrix (Fin n) (Fin n) ℝ) where
  coe A := A.mat

@[simp]
lemma SPD.transpose_eq_self {n : ℕ} (A : SPD n) :
    Matrix.transpose A.mat = A.mat := by
  simpa [Matrix.IsSymm] using A.symm

lemma SPD.posDef {n : ℕ} (A : SPD n) : A.mat.PosDef :=
  A.pos

end InfoGeometry.Jordan
