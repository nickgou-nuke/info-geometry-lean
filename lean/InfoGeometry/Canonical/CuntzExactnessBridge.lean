import InfoGeometry.Canonical.CuntzPrimitiveExactness

/-!
# Cuntz exactness bridge

This file adds the discrete derivative readout for the existing Cuntz/Cantor
projection layer.

The continuous side remains Mathlib/`PrimitiveExactness`: exact complex forms on
open sets imply zero rectangular holonomy.  The discrete side is the repository's
`CuntzO2Carrier`, whose range partition

`S_left * star S_left + S_right * star S_right = 1`

makes the unit/vacuum a closed element for the Cuntz branch derivative.

No theorem here asserts `K₁(O₂) = 0`, derives Cuntz isometries from analytic
holonomy, or derives analytic primitive exactness from Cuntz data.  The bridge is
a synchronized consequence of explicit analytic and Cuntz premises.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzExactnessBridge

open Complex
open InfoGeometry.Canonical.PrimitiveExactness
open InfoGeometry.Canonical.ZeroHolonomyAnalyticity
open InfoGeometry.Topology

open scoped Topology

variable {Op : Type*} [Ring Op] [StarRing Op]

/--
The discrete exterior derivative on a Cuntz/Cantor operator carrier.

It measures the defect between an operator `A` and the sum of its two Cuntz
branch descendants.
-/
@[rep_depth operator]
def cuntzDerivative (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (A : Op) : Op :=
  A - (InfoGeometry.Topology.CuntzO2Carrier.S_left C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))

@[rep_depth operator]
theorem cuntzDerivative_add
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (A B : Op) :
    cuntzDerivative C (A + B) = cuntzDerivative C A + cuntzDerivative C B := by
  unfold cuntzDerivative
  simp only [add_mul, mul_add]
  abel

/--
The Cuntz vacuum/unit is exact for the discrete derivative.

This is exactly the range partition of unity, rewritten as a zero-defect
statement for `A = 1`.
-/
@[rep_depth operator]
theorem cuntz_vacuum_is_exact (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    cuntzDerivative C 1 = 0 := by
  unfold cuntzDerivative
  calc
    1 - (InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))
        = 1 - (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) := by
            simp
    _ = 1 - 1 := by
          rw [InfoGeometry.Topology.CuntzO2Carrier.range_sum C]
    _ = 0 := by
          exact sub_self 1

/--
Zero Cuntz derivative is precisely lossless branch reconstruction.
-/
@[rep_depth operator]
theorem cuntzDerivative_eq_zero_iff (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (A : Op) :
    cuntzDerivative C A = 0 ↔
      A = InfoGeometry.Topology.CuntzO2Carrier.S_left C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  unfold cuntzDerivative
  exact sub_eq_zero

/--
An exact state has no Cuntz branch defect: it reconstructs from its two children.
-/
@[rep_depth operator]
theorem exactness_prevents_anomaly (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (A : Op)
    (h_exact : cuntzDerivative C A = 0) :
    A = InfoGeometry.Topology.CuntzO2Carrier.S_left C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * A * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  exact (cuntzDerivative_eq_zero_iff C A).mp h_exact

/--
The vacuum exactness theorem restated as explicit branch reconstruction.
-/
@[rep_depth operator]
theorem cuntz_vacuum_branch_reconstruction (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (1 : Op) = InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  exact exactness_prevents_anomaly C 1 (cuntz_vacuum_is_exact C)

/--
Synchronized continuous/discrete exactness bridge.

Analytic primitive exactness gives zero rectangular holonomy on the complex side;
the explicit Cuntz carrier gives exactness of the discrete vacuum on the branch
side.
-/
@[rep_depth operator]
theorem primitiveExactOn_with_cuntz_vacuum_exact
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hExact : IsExactOn f U)
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    ZeroRectangularHolonomyOn f U ∧ cuntzDerivative C 1 = 0 := by
  exact ⟨primitiveExactOn_to_zeroRectangularHolonomyOn hU hExact,
    cuntz_vacuum_is_exact C⟩

/--
Disk-local holomorphic version of the continuous/discrete exactness bridge.
-/
@[rep_depth operator]
theorem differentiableOn_ball_with_cuntz_vacuum_exact
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    ZeroRectangularHolonomyOn f (Metric.ball c r) ∧ cuntzDerivative C 1 = 0 := by
  exact primitiveExactOn_with_cuntz_vacuum_exact
    Metric.isOpen_ball (differentiableOn_ball_to_isExactOn hf) C

end InfoGeometry.Canonical.CuntzExactnessBridge

end noncomputable section
