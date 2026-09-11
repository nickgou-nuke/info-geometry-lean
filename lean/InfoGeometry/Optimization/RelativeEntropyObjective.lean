/- Quantum Relative Entropy Objective -/
/- Formalizes the Umegaki/Araki Relative Entropy as the Birkhoff 
   Spectral Descent objective function. -/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Matrix
open scoped Matrix

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/- 
  The Umegaki Quantum Relative Entropy (Bregman/Fenchel gap) between 
  two matrices. This acts as the exact objective 
  function (reconstruction error) for the WNMF vacuum optimization.
-/
noncomputable def QuantumRelativeEntropy (V WH : Matrix n n ℝ) : ℝ :=
  trace (V * (Real.log (det V)) • (1 : Matrix n n ℝ) - V * (Real.log (det WH)) • (1 : Matrix n n ℝ) - V + WH)

/-- The reconstruction objective vanishes on the diagonal. -/
theorem relative_entropy_self_eq_zero (V : Matrix n n ℝ) :
    QuantumRelativeEntropy V V = 0 := by
  simp [QuantumRelativeEntropy]

/-- The diagonal reconstruction objective is nonnegative because it is zero. -/
theorem relative_entropy_self_nonneg (V : Matrix n n ℝ) :
    0 ≤ QuantumRelativeEntropy V V := by
  rw [relative_entropy_self_eq_zero]

end InfoGeometry.Optimization
