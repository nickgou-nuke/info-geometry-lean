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

We treat a finite real matrix as a linear operator on the space of functions
`α → ℝ`. The map `Matrix.toLin'` provides the canonical mathlib embedding

`Matrix α α ℝ → ((α → ℝ) →ₗ[ℝ] (α → ℝ))`.

This embedding respects the positive gauge scalar action because scalar
multiplication of matrices corresponds to scalar multiplication of the resulting
linear maps.

This layer is only the matrix-to-operator functor. It does not assert positivity,
self-adjointness, spectral theory, Wick normal ordering, or current anomalies.
-/

namespace InfoGeometry.Stratum

open Matrix

noncomputable section

/--
A structure representing the functor from finite matrices to linear operators.

The `toFun` field sends a matrix to the associated linear map via
`Matrix.toLin'`. The proof `map_smul'` records compatibility with the positive
scalar gauge action.
-/
structure OperatorFunctor (α : Type*) [Fintype α] where
  toFun : Matrix α α ℝ → (α → ℝ) →ₗ[ℝ] (α → ℝ)
  map_smul' : ∀ (c : ℝ) (_hc : 0 < c) (M : Matrix α α ℝ),
    toFun (c • M) = c • toFun M

/-- The canonical operator functor using `Matrix.toLin'`. -/
def operatorFunctor {α : Type*} [Fintype α] : OperatorFunctor α := by
  classical
  refine
    { toFun := fun M => Matrix.toLin' M
      map_smul' := ?_ }
  intro c _hc M
  ext v i
  simp [Matrix.toLin'_apply, Pi.smul_apply]

/-- Exposed rewrite lemma for downstream stratum files. -/
@[simp]
theorem operatorFunctor_map_smul {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 < c) (M : Matrix α α ℝ) :
    (operatorFunctor (α := α)).toFun (c • M)
      =
    c • (operatorFunctor (α := α)).toFun M :=
  (operatorFunctor (α := α)).map_smul' c hc M

end

end InfoGeometry.Stratum
