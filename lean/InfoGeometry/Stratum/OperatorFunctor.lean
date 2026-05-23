import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.Stratum.Gauge
import InfoGeometry.Stratum.DiagonalFunctor

/-!
# InfoGeometry.Stratum.OperatorFunctor

Layer 2 → Layer 3 functorial embedding.

We treat a positive definite matrix (finite non‑commutative layer) as a linear
operator on the space of functions `α → ℝ`. The map `Matrix.toLinearMap`
provides a canonical embedding of `Matrix α α ℝ` into `LinearMap ℝ (α → ℝ) (α → ℝ)`.
This embedding respects the `PosGauge` scalar action because scalar
multiplication of matrices corresponds to scalar multiplication of the
resulting linear maps.
-/

namespace InfoGeometry.Stratum

open Matrix

noncomputable section

/-- A structure representing the functor from finite matrices to linear operators.
The `toFun` field sends a matrix to the associated linear map via
`Matrix.toLinearMap`. The proof `map_smul'` records compatibility with the
scalar gauge action. -/
structure OperatorFunctor (α : Type*) [Fintype α] where
  toFun : Matrix α α ℝ → (α → ℝ) →ₗ[ℝ] (α → ℝ)
  map_smul' : ∀ (c : ℝ) (hc : 0 < c) (M : Matrix α α ℝ),
    toFun (c • M) = c • toFun M

/-- The canonical operator functor using `Matrix.toLinearMap`. -/
def operatorFunctor {α : Type*} [Fintype α] : OperatorFunctor α :=
  { toFun := fun M => Matrix.toLinearMap M
    map_smul' := by
      intro c hc M
      -- scalar multiplication of matrices commutes with `toLinearMap`
      ext v i
      simp [Matrix.toLinearMap, smul_mul_assoc, smul_eq_mul, Pi.smul_apply] }

end InfoGeometry.Stratum
