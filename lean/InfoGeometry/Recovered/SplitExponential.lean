import Mathlib.Tactic
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Split-Quaternion Exponentials

This file formalizes the matrix exponential of the split-quaternion generators, 
showing exactly how the choice of signature affects the resulting geometric 
transformation (Euler rotations vs. hyperbolic rotations).

For `splitI` (which squares to `-1` in this matrix representation), the
matrix exponential is the trigonometric one.  This is a rotation-like one-
parameter subgroup, not a hyperbolic Lorentz-boost rapidity.
-/

namespace InfoGeometry.SplitExponential

open InfoGeometry.SplitQuaternion

/--
The Matrix Exponential for `splitI`.
Since `splitI * splitI = -splitOne`, the Taylor expansion of `exp(ϕ * splitI)`
separates into even (cosine) and odd (sine) terms exactly like Euler's formula.
-/
noncomputable def expSplitI (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.cos ϕ) • splitOne + (Real.sin ϕ) • splitI

/--
The algebraic verification that `splitI` squares to `-splitOne`.  This is the
reason its exponential has sine/cosine coefficients.
-/
theorem splitI_sq_is_neg_identity :
  splitI * splitI = -splitOne := splitI_sq

/--
The addition formula for the trigonometric exponential.  Multiplication of
these matrices corresponds to addition of the angle parameter.
-/
theorem expSplitI_add (ϕ ψ : ℝ) :
  expSplitI (ϕ + ψ) = expSplitI ϕ * expSplitI ψ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [expSplitI, splitOne, splitI, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;>
    ring

end InfoGeometry.SplitExponential
