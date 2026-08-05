/-
InfoGeometry/Geometry/RealSiegelSpace.lean

Pure real Siegel substrate for the higher-rank symplectic lane.
No complex imports.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.SymplecticGroup

noncomputable section

namespace InfoGeometry.Geometry.Cartan

/-- Real `n × n` matrices. -/
abbrev MatrixN (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℝ

/-
Pure real Siegel space.

Classically one writes `Z = X + iY`; here we keep the real pair `(X,Y)` and
remember that `Y` is positive definite.
-/
/-- A symmetric real matrix. -/
abbrev SymmetricMatrix (n : ℕ) :=
  {M : MatrixN n // M.IsSymm}

/-- A symmetric positive-definite real matrix. -/
abbrev SymmetricPosDefMatrix (n : ℕ) :=
  {M : MatrixN n // M.IsSymm ∧ Matrix.PosDef M}

/-- Native subtype/product model of real Siegel space. -/
abbrev RealSiegelSpace (n : ℕ) :=
  SymmetricMatrix n × SymmetricPosDefMatrix n

namespace RealSiegelSpace

abbrev X (Z : RealSiegelSpace n) : MatrixN n := Z.1.1
abbrev Y (Z : RealSiegelSpace n) : MatrixN n := Z.2.1
abbrev X_symm (Z : RealSiegelSpace n) : Z.X.IsSymm := Z.1.2
abbrev Y_symm (Z : RealSiegelSpace n) : Z.Y.IsSymm := Z.2.2.1
abbrev Y_posDef (Z : RealSiegelSpace n) : Matrix.PosDef Z.Y := Z.2.2.2

@[ext] theorem ext {p q : RealSiegelSpace n}
    (hX : p.X = q.X) (hY : p.Y = q.Y) : p = q := by
  rcases p with ⟨⟨pX, hpX⟩, ⟨pY, hpYsymm, hpYpos⟩⟩
  rcases q with ⟨⟨qX, hqX⟩, ⟨qY, hqYsymm, hqYpos⟩⟩
  dsimp [X, Y] at hX hY
  cases hX
  cases hY
  rfl

end RealSiegelSpace

/-- The real symplectic group `Sp(2n, ℝ)`. -/
abbrev Sp2nR (n : ℕ) : Type :=
  Matrix.symplecticGroup (Fin n) ℝ

end InfoGeometry.Geometry.Cartan
