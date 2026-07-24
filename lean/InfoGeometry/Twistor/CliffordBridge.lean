import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import InfoGeometry.Twistor.PenroseTwistor

/-!
# Twistor sesquilinear-to-Clifford bridge

This file is the narrow algebraic bridge that was still missing after the
repo-wide scan:

* the Penrose twistor Hermitian form is already owned in
  `InfoGeometry.Twistor.PenroseTwistor`;
* its real part gives a real bilinear/quadratic substrate;
* that quadratic substrate canonically defines a Clifford algebra;
* any quadratic isometry of the twistor carrier lifts to a Clifford algebra
  map by mathlib's `CliffordAlgebra.map`.

This does not assert any new geometric equivalence beyond the quadratic-form
bridge.  It makes the bilinear/Clifford and equivariance surfaces explicit.
-/

open scoped Classical

namespace InfoGeometry.Twistor.CliffordBridge

open PenroseTwistor

abbrev TwistorClifford : Type :=
  CliffordAlgebra PenroseTwistor.twistorRealQuadraticForm

/-- The Penrose real bilinear readout polarizes to the underlying quadratic form. -/
theorem twistorRealQuadraticForm_polar (z w : TwistorCarrier) :
    QuadraticMap.polar PenroseTwistor.twistorRealQuadraticForm z w
      = PenroseTwistor.twistorRealBilinear z w + PenroseTwistor.twistorRealBilinear w z := by
  simpa [PenroseTwistor.twistorRealQuadraticForm] using
    (LinearMap.BilinMap.polar_toQuadraticMap
      (R := ℝ) (M := TwistorCarrier) (N := ℝ) (B := PenroseTwistor.twistorRealBilinear) z w)

/-- The Clifford anticommutator reads back the polar form of the Penrose substrate. -/
@[simp] theorem twistorClifford_ι_mul_ι_add_swap_eq_polar
    (z w : TwistorCarrier) :
    CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm z * CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm w
      + CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm w * CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm z
        = algebraMap ℝ TwistorClifford (QuadraticMap.polar PenroseTwistor.twistorRealQuadraticForm z w) := by
  simpa [TwistorClifford] using
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := PenroseTwistor.twistorRealQuadraticForm) z w)

/-- The Clifford anticommutator reads back the explicit Penrose bilinear readout. -/
@[simp] theorem twistorClifford_ι_mul_ι_add_swap_eq_bilinear
    (z w : TwistorCarrier) :
    CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm z * CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm w
      + CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm w * CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm z
        = algebraMap ℝ TwistorClifford (PenroseTwistor.twistorRealBilinear z w + PenroseTwistor.twistorRealBilinear w z) := by
  rw [twistorClifford_ι_mul_ι_add_swap_eq_polar, twistorRealQuadraticForm_polar]

/--
A quadratic isometry of the twistor carrier.

This is the honest equivariance socket: it states exactly the preservation law
that is needed before `CliffordAlgebra.map` can be applied.
-/
structure TwistorQuadraticEquivariance (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier) : Prop where
  preserves : ∀ z, PenroseTwistor.twistorRealQuadraticForm (f z) = PenroseTwistor.twistorRealQuadraticForm z

/-- Convert a quadratic-equivariant linear equivalence into a mathlib isometry. -/
def toTwistorQuadraticIsometry
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) :
    PenroseTwistor.twistorRealQuadraticForm →qᵢ PenroseTwistor.twistorRealQuadraticForm where
  __ := f.toLinearMap
  map_app' := h.preserves

/-- The induced Clifford algebra map from an equivariant twistor isometry. -/
noncomputable def twistorCliffordMap
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) :
    TwistorClifford →ₐ[ℝ] TwistorClifford :=
  CliffordAlgebra.map (toTwistorQuadraticIsometry f h)

@[simp] theorem twistorCliffordMap_apply_ι
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) (z : TwistorCarrier) :
    twistorCliffordMap f h (CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm z)
      = CliffordAlgebra.ι PenroseTwistor.twistorRealQuadraticForm (f z) := by
  rw [twistorCliffordMap, CliffordAlgebra.map_apply_ι]
  rfl

end InfoGeometry.Twistor.CliffordBridge
