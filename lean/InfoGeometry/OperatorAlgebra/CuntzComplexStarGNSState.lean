/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductPositivity
import InfoGeometry.Prequantum.GNSAction

/-! The existing real algebraic GNS construction applied to the positive
functional on the corrected complex Cuntz quotient. No completion is asserted. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open scoped ComplexOrder
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSAction

/-- Realification of the positive complex quotient functional. -/
def quotientProductRealState (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (hpos : ∀ i, 0 ≤ q i) : RealAlgebraicState (ComplexStarCuntzAlg Bool) where
  toLinearMap := Complex.reLm.comp ((quotientProductFunctional q hq).restrictScalars ℝ)
  normalized := by
    change (quotientProductFunctional q hq 1).re = 1
    rw [quotientProductFunctional_one]
    rfl
  positive x := (Complex.nonneg_iff.mp (quotientProductFunctional_nonneg q hq hpos x)).1
  symmetric x y := by
    change (quotientProductFunctional q hq (star y * x)).re =
      (quotientProductFunctional q hq (star x * y)).re
    have h := congrArg Complex.re (quotientProductFunctional_star q hq (star x * y))
    simpa only [star_mul, star_star, Complex.star_def, Complex.conj_re] using h

/-- The real GNS null condition is precisely the complex quadratic null condition. -/
theorem quotientProductRealState_null_iff (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (hpos : ∀ i, 0 ≤ q i) (x : ComplexStarCuntzAlg Bool) :
    x ∈ (quotientProductRealState q hq hpos).gnsNullSet ↔
      quotientProductFunctional q hq (star x * x) = 0 := by
  change (quotientProductFunctional q hq (star x * x)).re = 0 ↔ _
  have him := (Complex.nonneg_iff.mp (quotientProductFunctional_nonneg q hq hpos x)).2
  constructor
  · intro hre
    apply Complex.ext
    · exact hre
    · exact him.symm
  · intro h
    rw [h]
    rfl

/-- The left-ideal condition for the existing quotient action is a theorem. -/
def quotientProductRepresentationState (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (hpos : ∀ i, 0 ≤ q i) : RepresentationState (ComplexStarCuntzAlg Bool) where
  state := ⟨quotientProductRealState q hq hpos⟩
  null_left_ideal a _x hx :=
    (quotientProductRealState q hq hpos).mul_mem_gnsNullSet a hx

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
