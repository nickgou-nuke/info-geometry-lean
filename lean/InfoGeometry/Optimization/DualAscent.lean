/- Dual Ascent Optimization Loop -/
/- Implements the loxodromic flow driver for Birkhoff Spectral Descent.
   Takes gradient G, extracts unitary direction via msign(G) (Polar),
   steps along tangent cone, and retracts via Dykstra. -/

import InfoGeometry.Optimization.PolarDecomposition
import InfoGeometry.Optimization.Dykstra
import InfoGeometry.Optimization.BirkhoffPolytope

open Matrix

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/- 
  The Loxodromic Dual Ascent Step.
  1. Computes the gradient step direction via msign(G) (Polar Unitary factor).
  2. Moves the state along the tangent cone.
  3. Retracts the intermediate state back onto the Birkhoff Polytope via Dykstra.
-/
noncomputable def DualAscentStep (W : Matrix n n ℝ) (G : Matrix n n ℝ) (G_pinv : Matrix n n ℝ) 
    (η : ℝ) (iters : ℕ) : Matrix n n ℝ :=
  let U := PolarNewtonStep G G_pinv
  let W_temp := BirkhoffDualAscentStep W U η
  BirkhoffRetraction W_temp iters

end InfoGeometry.Optimization