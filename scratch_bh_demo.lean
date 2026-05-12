-- browser-harness demo: scratch file fixed after looking up Mathlib4 docs
-- browser-harness found: Matrix.det_mul, Matrix.det_smul, Matrix.det_pow
-- browser-harness found: CommRing ℝ lives in Mathlib.Data.Real.Basic
-- Determinant is MULTIPLICATIVE, not additive.
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic

-- Correct: det is multiplicative (looked up via browser-harness → Mathlib4 docs)
example (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) :
    (A * B).det = A.det * B.det := by
  exact Matrix.det_mul A B

-- Correct: scalar multiple of det (looked up via browser-harness → Matrix.det_smul)
example (n : Type) [Fintype n] [DecidableEq n] (c : ℝ) (A : Matrix n n ℝ) :
    (c • A).det = c ^ Fintype.card n * A.det := by
  exact Matrix.det_smul A c
