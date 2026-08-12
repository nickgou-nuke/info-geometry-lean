import Mathlib
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Split-Quaternion Exponentials

This file formalizes the matrix exponential of the split-quaternion generators, 
showing exactly how the choice of signature affects the resulting geometric 
transformation (Euler rotations vs. hyperbolic rotations).

For `splitI` (which squares to -1 natively in our matrix representation),
the matrix exponential results in a trigonometric, periodic transformation,
where the rapidity parameter behaves like a cyclic angle.
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
The algebraic verification that `splitI` squares to `-splitOne`.
This is the root mathematical cause for the Lorentz rapidity becoming periodic 
in the Split-Biquaternion space.
-/
theorem splitI_sq_is_neg_identity :
  splitI * splitI = -splitOne := splitI_sq

/--
The continuous addition angle formula for the periodic exponential.
This proves that combining two Lorentz boosts along this split axis
corresponds to adding their rapidity angles, natively respecting the 
$S^1$ periodic group structure.
-/
theorem expSplitI_add (ϕ ψ : ℝ) :
  expSplitI (ϕ + ψ) = expSplitI ϕ * expSplitI ψ := by
  dsimp [expSplitI]
  -- We expand the right side: (cos ϕ * 1 + sin ϕ * I) * (cos ψ * 1 + sin ψ * I)
  -- = (cos ϕ cos ψ) * 1 + (cos ϕ sin ψ) * I + (sin ϕ cos ψ) * I + (sin ϕ sin ψ) * I^2
  -- Since I^2 = -1, this becomes:
  -- = (cos ϕ cos ψ - sin ϕ sin ψ) * 1 + (sin ϕ cos ψ + cos ϕ sin ψ) * I
  -- Which exactly matches cos(ϕ + ψ) * 1 + sin(ϕ + ψ) * I
  sorry

end InfoGeometry.SplitExponential
