/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarGNSQuotient

/-! The native radical action as a unital complex algebra representation,
with adjoint compatibility for the descended pairing and a cyclic vacuum.
No boundedness, completion, or faithfulness is asserted. -/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open Archetype_II_GNS_Radical

variable (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)

@[simp] theorem quotientProductRadicalAction_mk (a x : ComplexStarCuntzAlg Bool) :
    quotientProductRadicalAction q hq a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (a * x) := rfl

/-- The existing left action preserves the full unital complex algebra structure. -/
def quotientProductGNSAlgHom : ComplexStarCuntzAlg Bool →ₐ[ℂ]
    Module.End ℂ
      (ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) where
  toFun := quotientProductRadicalAction q hq
  map_zero' := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    change Submodule.Quotient.mk (0 * x) = (0 :
      ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq))
    simp
  map_one' := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    change Submodule.Quotient.mk (1 * x) = Submodule.Quotient.mk x
    rw [one_mul]
  map_add' a b := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    change Submodule.Quotient.mk ((a + b) * x) =
      (Submodule.Quotient.mk (a * x) + Submodule.Quotient.mk (b * x) :
        ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq))
    rw [add_mul, Submodule.Quotient.mk_add]
  map_mul' a b := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    change Submodule.Quotient.mk ((a * b) * x) = Submodule.Quotient.mk (a * (b * x))
    rw [mul_assoc]
  commutes' c := by
    apply LinearMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    intro x
    change Submodule.Quotient.mk (algebraMap ℂ (ComplexStarCuntzAlg Bool) c * x) =
      (c • Submodule.Quotient.mk x :
        ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq))
    rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]

/-- Multiplication by the involution is the adjoint for the actual GNS pairing. -/
theorem quotientProductRadicalAction_adjoint (a : ComplexStarCuntzAlg Bool)
    (z w : ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) :
    quotientProductPairingDescended q hq (quotientProductRadicalAction q hq a z) w =
      quotientProductPairingDescended q hq z (quotientProductRadicalAction q hq (star a) w) := by
  refine Quotient.inductionOn₂ z w ?_
  intro x y
  change quotientProductFunctional q hq (star (a * x) * y) =
    quotientProductFunctional q hq (star x * (star a * y))
  rw [star_mul, mul_assoc]

/-- Every algebraic quotient vector is an operator applied to the vacuum class. -/
theorem quotientProductGNS_vacuum_cyclic
    (z : ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) :
    ∃ a : ComplexStarCuntzAlg Bool,
      quotientProductGNSAlgHom q hq a (Submodule.Quotient.mk 1) = z := by
  refine Quotient.inductionOn z ?_
  intro x
  refine ⟨x, ?_⟩
  change Submodule.Quotient.mk (x * 1) = Submodule.Quotient.mk x
  rw [mul_one]

/-- The vacuum matrix coefficient recovers the original quotient functional. -/
theorem quotientProductGNS_vacuum_expectation (a : ComplexStarCuntzAlg Bool) :
    quotientProductPairingDescended q hq (Submodule.Quotient.mk 1)
      (quotientProductGNSAlgHom q hq a (Submodule.Quotient.mk 1)) =
        quotientProductFunctional q hq a := by
  change quotientProductFunctional q hq (star (1 : ComplexStarCuntzAlg Bool) * (a * 1)) = _
  rw [star_one, one_mul, mul_one]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
