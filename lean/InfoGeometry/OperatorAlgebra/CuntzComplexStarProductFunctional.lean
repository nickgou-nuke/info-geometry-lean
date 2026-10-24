/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarCoreRetraction
import InfoGeometry.QuantumContext.MatrixProductState

/-! A normalized, star-preserving product functional on the corrected quotient.
The positivity theorem here is restricted to squares of elements of the core.
The separate `CuntzComplexStarProductPositivity` module proves positivity on
arbitrary quotient squares. KMS remains a further obligation. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
open InfoGeometry.QuantumContext.MatrixStageProductDensity
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection

def quotientProductFunctional (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1) :
    ComplexStarCuntzAlg Bool →ₗ[ℂ] ℂ :=
  (productFunctional q hq).comp coreRetraction

@[simp] theorem quotientProductFunctional_embed (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (x : Carrier) :
    quotientProductFunctional q hq (quotientHom x) = productFunctional q hq x := by
  simp [quotientProductFunctional]

@[simp] theorem quotientProductFunctional_one (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) : quotientProductFunctional q hq 1 = 1 := by
  simp [quotientProductFunctional, productFunctional_one]

theorem quotientProductFunctional_star (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (x : ComplexStarCuntzAlg Bool) :
    quotientProductFunctional q hq (star x) = star (quotientProductFunctional q hq x) := by
  simp [quotientProductFunctional, coreRetraction_star, productFunctional_star]

open scoped ComplexOrder in
theorem quotientProductFunctional_embed_nonneg (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (hpos : ∀ i, 0 ≤ q i) (x : Carrier) :
    0 ≤ quotientProductFunctional q hq (star (quotientHom x) * quotientHom x) := by
  rw [← map_star, ← map_mul, quotientProductFunctional_embed]
  exact productFunctional_nonneg q hq hpos x

open scoped ComplexOrder in
theorem quotientProductFunctional_core_nonneg (q : Fin 2 → ℝ)
    (hq : q 0 + q 1 = 1) (hpos : ∀ i, 0 ≤ q i)
    (x : ComplexStarCuntzAlg Bool) (hx : x ∈ core) :
    0 ≤ quotientProductFunctional q hq (star x * x) := by
  rw [← range_quotientAlgHom] at hx
  obtain ⟨y, rfl⟩ := hx
  exact quotientProductFunctional_embed_nonneg q hq hpos y

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
