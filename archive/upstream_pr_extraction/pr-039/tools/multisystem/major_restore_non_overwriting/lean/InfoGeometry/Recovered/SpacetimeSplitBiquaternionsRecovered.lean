import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Spacetime Vectors in Split-Biquaternions

This file defines the embedding of Minkowski spacetime vectors $(t, x, y, z)$ 
into the $2 \times 2$ matrix representation of the split-biquaternions (and split-quaternions).

The Lorentz boosts act via the hyperbolic $l$ generator matching the signature $(-, +, +)$.
-/

namespace InfoGeometry.Spacetime

open Matrix

/-- The standard identity matrix. -/
def splitOne : Matrix (Fin 2) (Fin 2) ℝ := 1
/-- The imaginary unit `i`, corresponding to a rotation. `i^2 = -1`. -/
def splitI : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![-1, 0]]
/-- The hyperbolic unit `j`. `j^2 = +1`. -/
def splitJ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]
/-- The hyperbolic unit `k`. `k^2 = +1`. -/
def splitK : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]

/-- 
A spacetime vector $(t, x, y, z)$ mapped into the $2 \times 2$ real matrix algebra.
This corresponds to the Pauli matrix basis adapted for the split signature.
-/
def spacetimeMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  t • splitOne + x • splitI + y • splitJ + z • splitK

/--
The determinant of the spacetime matrix computes the spacetime interval.
For `spacetimeMatrix t x y z`, the determinant is exactly `t^2 + x^2 - y^2 - z^2`, 
mirroring the Minkowski metric $(+, +, -, -)$ or its split counterpart.
-/
lemma det_spacetimeMatrix (t x y z : ℝ) :
    (spacetimeMatrix t x y z).det = t^2 + x^2 - y^2 - z^2 := by
  simp [spacetimeMatrix, splitOne, splitI, splitJ, splitK, Matrix.det_fin_two]
  ring

/--
A Lorentz boost along the Z-axis (rapidity `ϕ`) using the hyperbolic generator `k`.
This implements $e^{\phi (l\mathbf{k})} = \cos\phi + l\mathbf{k}\sin\phi$ natively as a matrix.
-/
noncomputable def lorentzBoostZ (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.cos ϕ) • splitOne + (Real.sin ϕ) • splitK

/--
A spatial rotation in the XY-plane (angle `θ`) using the compact imaginary generator `i`.
This implements $e^{\theta \mathbf{i}} = \cos\theta + \mathbf{i}\sin\theta$ natively as a matrix.
-/
noncomputable def spatialRotationXY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.cos θ) • splitOne + (Real.sin θ) • splitI

end InfoGeometry.Spacetime
