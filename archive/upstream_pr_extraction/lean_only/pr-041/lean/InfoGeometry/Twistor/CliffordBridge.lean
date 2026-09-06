import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

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
open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.CliffordBridge

open PenroseTwistor
open InfoGeometry.Twistor.ProjectiveNullIsometryIncidence
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence

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
The exact quadratic-form preservation relation required by the Clifford map.

This is a direct proposition rather than a one-field evidence wrapper; the
relation is consumed by Mathlib's `QuadraticMap.Isometry` interface below.
-/
def TwistorQuadraticEquivariance
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier) : Prop :=
  ∀ z, PenroseTwistor.twistorRealQuadraticForm (f z) =
    PenroseTwistor.twistorRealQuadraticForm z

namespace TwistorQuadraticEquivariance

/-- Read the quadratic preservation relation under its historical field name. -/
theorem preserves
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) (z : TwistorCarrier) :
    PenroseTwistor.twistorRealQuadraticForm (f z) =
      PenroseTwistor.twistorRealQuadraticForm z :=
  h z

end TwistorQuadraticEquivariance

/-- Convert a quadratic-equivariant linear equivalence into a mathlib isometry. -/
def toTwistorQuadraticIsometry
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) :
    PenroseTwistor.twistorRealQuadraticForm →qᵢ PenroseTwistor.twistorRealQuadraticForm where
  __ := f.toLinearMap
  map_app' := h.preserves

/-- Package the same Penrose quadratic symmetry as an equivalence, reusing the
native Mathlib `QuadraticMap.IsometryEquiv` interface. -/
def toTwistorQuadraticIsometryEquiv
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f) :
    PenroseTwistor.twistorRealQuadraticForm.IsometryEquiv
      PenroseTwistor.twistorRealQuadraticForm where
  toLinearEquiv := f
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

/--
The projectivization of a Penrose quadratic isometry preserves the real null
twistor boundary.  This is the concrete Penrose specialization of the
generic projective-null isometry theorem; no second projectivization API is
introduced here.
-/
theorem projectiveTwistorIsometryMap_preserves_null
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f)
    (p : ℙ ℝ TwistorCarrier) :
    IsNull PenroseTwistor.twistorRealQuadraticForm p →
      IsNull PenroseTwistor.twistorRealQuadraticForm
        (projectiveIsometryMap (toTwistorQuadraticIsometryEquiv f h) p) := by
  exact projectiveIsometryMap_preserves_null
    (toTwistorQuadraticIsometryEquiv f h) p

/--
The same Penrose specialization preserves polar incidence on the real null
projective boundary.  The proof is transported entirely through Mathlib's
quadratic-isometry/projectivization API.
-/
theorem projectiveTwistorIsometryEquiv_preserves_incidence
    (f : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier)
    (h : TwistorQuadraticEquivariance f)
    (p q : RealNullTwistorSpace) :
    NullPolarIncident PenroseTwistor.twistorRealQuadraticForm
        (nullIsometryEquiv (toTwistorQuadraticIsometryEquiv f h) p)
        (nullIsometryEquiv (toTwistorQuadraticIsometryEquiv f h) q) ↔
      NullPolarIncident PenroseTwistor.twistorRealQuadraticForm p q := by
  exact nullIsometryEquiv_preserves_incidence
    (toTwistorQuadraticIsometryEquiv f h) p q

end InfoGeometry.Twistor.CliffordBridge
