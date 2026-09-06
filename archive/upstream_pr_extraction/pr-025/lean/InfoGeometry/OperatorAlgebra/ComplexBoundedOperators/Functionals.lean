import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# CBO-002: inner-product functionals

AFP surface:

* `cblinfun_cinner_right`;
* `bounded_antilinear_cblinfun_cinner_right`.

Lean owner surface:

* `innerSL ℂ x : E →L[ℂ] ℂ`;
* `InnerProductSpace.toDualMap`.

This file exposes the continuous linear functional `y ↦ ⟪x, y⟫`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace Functionals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- AFP `cblinfun_cinner_right`: the bounded functional `y ↦ ⟪x, y⟫`. -/
def innerRight (x : E) : E →L[ℂ] ℂ :=
  innerSL ℂ x

@[simp]
theorem innerRight_apply (x y : E) :
    innerRight x y = @inner ℂ E _ x y := by
  simpa [innerRight] using innerSL_apply_apply (𝕜 := ℂ) (E := E) x y

/-- The inner-product functional has norm `‖x‖`. -/
@[simp]
theorem norm_innerRight (x : E) :
    ‖innerRight x‖ = ‖x‖ := by
  simpa [innerRight] using innerSL_apply_norm (𝕜 := ℂ) (E := E) x

/-- `innerRight` is the continuous-linear-map view of mathlib's Riesz embedding. -/
theorem innerRight_eq_toDualMap (x : E) :
    innerRight x = InnerProductSpace.toDualMap ℂ E x := by
  rfl

end Functionals
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
