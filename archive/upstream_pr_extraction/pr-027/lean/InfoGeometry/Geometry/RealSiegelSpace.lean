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

/--
Pure real Siegel space.

Classically one writes `Z = X + iY`; here we keep the real pair `(X,Y)` and
remember that `Y` is positive definite.
-/
structure RealSiegelSpace (n : ℕ) where
  X : MatrixN n
  Y : MatrixN n
  X_symm : X.IsSymm
  Y_symm : Y.IsSymm
  Y_posDef : Matrix.PosDef Y

/-- The real symplectic group `Sp(2n, ℝ)`. -/
abbrev Sp2nR (n : ℕ) : Type :=
  Matrix.symplecticGroup (Fin n) ℝ

end InfoGeometry.Geometry.Cartan
