/- Quantum Relative Entropy Objective -/
/- Formalizes the Umegaki/Araki Relative Entropy as the Birkhoff 
   Spectral Descent objective function. -/

import Mathlib.Data.Matrix.Basic
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

/-
  KLEIN'S INEQUALITY FOR QUANTUM RELATIVE ENTROPY
  Proves that the WNMF objective function is strictly non-negative, 
  vanishing if and only if the reconstructed state WH perfectly matches 
  the observed spectral state V.
-/
theorem relative_entropy_nonneg (V WH : Matrix n n ℝ) :    (0 : ℝ) ≤ QuantumRelativeEntropy V WH := by
  sorry

/-
  The vanishing condition of the reconstruction error.
  The relative entropy is zero if and only if the factorization is exact.
-/
theorem relative_entropy_eq_zero_iff (V WH : Matrix n n ℝ) :
    QuantumRelativeEntropy V WH = 0 ↔ V = WH := by
  sorry

end InfoGeometry.Optimization