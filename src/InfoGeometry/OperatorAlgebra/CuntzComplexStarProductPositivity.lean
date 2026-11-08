/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
import InfoGeometry.Algebra.CuntzComplexStarHomogeneousPositivity

/-! Positivity on every star-square of the corrected binary Cuntz quotient.
The proof is finite algebraic degree decomposition, not analytic averaging. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open scoped ComplexOrder
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection
open InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

theorem coreRetraction_projection (x : ComplexStarCuntzAlg Bool) :
    coreRetraction (projection x) = coreRetraction x := by
  apply quotientHom_injective
  rw [quotientHom_coreRetraction, quotientHom_coreRetraction, projection_idempotent]

theorem quotientProductFunctional_projection (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (x : ComplexStarCuntzAlg Bool) :
    quotientProductFunctional q hq (projection x) = quotientProductFunctional q hq x := by
  simp only [quotientProductFunctional, LinearMap.comp_apply, coreRetraction_projection]

theorem quotientProductFunctional_nonneg (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (hpos : ∀ i, 0 ≤ q i)
    (x : ComplexStarCuntzAlg Bool) :
    0 ≤ quotientProductFunctional q hq (star x * x) := by
  rw [← quotientProductFunctional_projection q hq (star x * x),
    projection_star_mul, map_finsuppSum]
  apply Finset.sum_nonneg
  intro d _
  exact homogeneous_square_nonneg (quotientProductFunctional q hq)
    (quotientProductFunctional_core_nonneg q hq hpos) d
    (component d x) (delta_component d x)

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
