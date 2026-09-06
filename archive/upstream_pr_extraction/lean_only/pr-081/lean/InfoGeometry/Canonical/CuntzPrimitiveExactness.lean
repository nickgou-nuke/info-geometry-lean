import InfoGeometry.Canonical.PrimitiveExactness
import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# Cuntz primitive exactness

This file records the honest finite algebraic bridge between the analytic
primitive-exactness layer and the discrete Cuntz `O₂` projection layer.

The analytic side is Mathlib's `Complex.IsExactOn`: on an open complex domain it
implies zero rectangular holonomy through `PrimitiveExactness`.

The Cuntz side is the existing `CuntzO2Carrier`: its defining Cuntz relation and
orthogonal-range premise imply that the left and right range projections are
idempotent, orthogonal, and sum to the unit.  We do not claim that analytic
primitive exactness derives Cuntz isometries.  The bridge is a synchronized
readback from explicit premises on both sides.

#### BUCKET 1: CLOSED FINITE THEOREMS
The left/right Cuntz range projections are idempotent, orthogonal, sum to the
unit, and split every operator by left multiplication.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
Primitive exactness on an open complex domain plus an explicit Cuntz carrier
gives both zero rectangular holonomy and the Cuntz projection decomposition.

#### BUCKET 3: OPEN CLOSURE DEBT
No theorem here derives Cuntz isometries from holonomy, derives analytic
primitive exactness from a Cuntz carrier, or asserts a C*-completion/KMS/zeta
consequence.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzPrimitiveExactness

open Complex
open InfoGeometry.Canonical.PrimitiveExactness
open InfoGeometry.Canonical.ZeroHolonomyAnalyticity
open InfoGeometry.Topology

open scoped Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

/--
The discrete Cuntz projection exactness package.

For an explicit `CuntzO2Carrier`, the left and right range projections form an
orthogonal partition of the unit and split every operator.
-/
theorem cuntz_projection_exactness
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 1 ∧
    ∀ x : Op, (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x = x := by
  exact ⟨InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_idempotent C,
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_idempotent C,
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_mul_rightRangeProjection_eq_zero C,
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_mul_leftRangeProjection_eq_zero C,
    InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C,
    InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_decomposition C⟩

theorem cuntz_projection_decomposition_unique
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    {x y : Op}
    (hxy :
      (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x +
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x =
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * y +
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * y) :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x =
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * y ∧
      (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x =
        (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * y := by
  constructor
  · have hleft := congrArg
      (fun z : Op =>
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * z) hxy
    simpa [← mul_assoc, mul_add,
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_idempotent,
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_mul_rightRangeProjection_eq_zero]
      using hleft
  · have hright := congrArg
      (fun z : Op =>
        (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * z) hxy
    simpa [← mul_assoc, mul_add,
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_idempotent,
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_mul_leftRangeProjection_eq_zero]
      using hright

theorem cuntz_projection_decomposition_eq_iff
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    {x y : Op} :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x +
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x =
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * y +
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * y ↔
      ((InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x =
          (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * y ∧
        (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x =
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * y) := by
  constructor
  · exact cuntz_projection_decomposition_unique C
  · rintro ⟨hleft, hright⟩
    rw [hleft, hright]

/--
Primitive exactness and Cuntz projection exactness, stated without collapsing
one premise into the other.

The first component is the analytic zero-holonomy consequence of `IsExactOn`.
The remaining components are the finite Cuntz projection decomposition supplied
by the explicit `CuntzO2Carrier`.
-/
theorem primitiveExactOn_with_cuntz_projection_exactness
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U)
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    ZeroRectangularHolonomyOn f U ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 1 ∧
    ∀ x : Op, (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x = x := by
  exact ⟨primitiveExactOn_to_zeroRectangularHolonomyOn hU hExact,
    (cuntz_projection_exactness C).1,
    (cuntz_projection_exactness C).2.1,
    (cuntz_projection_exactness C).2.2.1,
    (cuntz_projection_exactness C).2.2.2.1,
    (cuntz_projection_exactness C).2.2.2.2.1,
    (cuntz_projection_exactness C).2.2.2.2.2⟩

/--
Disk-local version: holomorphicity on a ball gives primitive exactness there,
and an explicit Cuntz carrier gives the lossless left/right projection split.
-/
theorem differentiableOn_ball_with_cuntz_projection_exactness
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    ZeroRectangularHolonomyOn f (Metric.ball c r) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = 0 ∧
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = 1 ∧
    ∀ x : Op, (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * x + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * x = x := by
  exact primitiveExactOn_with_cuntz_projection_exactness
    Metric.isOpen_ball (differentiableOn_ball_to_isExactOn hf) C

end InfoGeometry.Canonical.CuntzPrimitiveExactness

end noncomputable section
