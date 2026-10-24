/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarGNSRadical

/-! The real GNS quotient and native complex radical quotient have exactly
the same representatives and left action. This is not a completion. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Prequantum.GNSBridge
open Archetype_II_GNS_Radical

variable (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1) (hpos : ∀ i, 0 ≤ q i)

/-- Identity on representatives identifies the two already-existing quotients. -/
def quotientProductGNSQuotientEquiv :
    (quotientProductRealState q hq hpos).GNSQuotient ≃
      ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq) :=
  Quotient.congr (Equiv.refl _) (by
    intro x y
    rw [Submodule.quotientRel_def]
    exact (quotientProduct_radical_iff q hq hpos (x - y)).symm)

@[simp] theorem quotientProductGNSQuotientEquiv_mk (x : ComplexStarCuntzAlg Bool) :
    quotientProductGNSQuotientEquiv q hq hpos
      (Quotient.mk (quotientProductRealState q hq hpos).gnsSetoid x) =
        Submodule.Quotient.mk x := rfl

/-- Left multiplication descends as a native complex-linear quotient operator. -/
def quotientProductRadicalAction (a : ComplexStarCuntzAlg Bool) :
    Module.End ℂ
      (ComplexStarCuntzAlg Bool ⧸ gnsRadical (quotientProductFunctional q hq)) :=
  (gnsRadical (quotientProductFunctional q hq)).mapQ
    (gnsRadical (quotientProductFunctional q hq)) (LinearMap.mulLeft ℂ a)
    (by
      intro x hx y
      change quotientProductFunctional q hq (star y * (a * x)) = 0
      simpa only [star_mul, star_star, mul_assoc] using hx (star a * y))

/-- The previously constructed GNS action is exactly the complex quotient action. -/
theorem quotientProductGNSQuotientEquiv_act (a : ComplexStarCuntzAlg Bool)
    (z : (quotientProductRealState q hq hpos).GNSQuotient) :
    quotientProductGNSQuotientEquiv q hq hpos
      ((quotientProductRepresentationState q hq hpos).act a z) =
    quotientProductRadicalAction q hq a (quotientProductGNSQuotientEquiv q hq hpos z) := by
  refine Quotient.inductionOn z ?_
  intro x
  rfl

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
