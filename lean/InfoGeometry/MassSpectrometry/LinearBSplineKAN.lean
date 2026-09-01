import Mathlib
import InfoGeometry.Analysis.ComplexBSpline
import InfoGeometry.MassSpectrometry.CausalCrossGramian

/-!
# Continuous linear B-spline specialization for causal KAN kernels

The repository already contains an analytic complex-B-spline corridor in
`InfoGeometry.Analysis.ComplexBSpline`.  For executable mass-spectrometry KAN
features we additionally need a small real, compactly supported basis with
fully elementary proofs.

`linearBSpline c w` is the triangular degree-one B-spline

`max 0 (1 - |x-c| / w)`

for positive width `w`.  We prove continuity, nonnegativity, unit value at the
center, and compact support.  A finite family of these basis functions then
instantiates the existing `FiniteKANCausalKernel` interface.

No universal Kolmogorov-Arnold approximation theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open scoped BigOperators

/-- Compactly supported triangular degree-one B-spline. -/
def linearBSpline (center width x : ℝ) : ℝ :=
  max 0 (1 - |x - center| / width)

/-- Linear B-splines are nonnegative without any width hypothesis. -/
theorem linearBSpline_nonneg (center width x : ℝ) :
    0 ≤ linearBSpline center width x := by
  exact le_max_left _ _

/-- Positive-width linear B-splines attain value one at their center. -/
@[simp] theorem linearBSpline_at_center
    (center width : ℝ) (hwidth : 0 < width) :
    linearBSpline center width center = 1 := by
  simp [linearBSpline, hwidth.ne']

/-- Outside the closed width-radius support the linear B-spline vanishes. -/
theorem linearBSpline_eq_zero_of_width_le_abs
    {center width x : ℝ} (hwidth : 0 < width)
    (hout : width ≤ |x - center|) :
    linearBSpline center width x = 0 := by
  have hratio : 1 ≤ |x - center| / width := by
    apply (le_div_iff₀ hwidth).2
    simpa using hout
  have hnonpos : 1 - |x - center| / width ≤ 0 := sub_nonpos.mpr hratio
  simp [linearBSpline, max_eq_left hnonpos]

/-- The real triangular B-spline is continuous for every fixed center and
nonzero width.  (The formula is also continuous at width zero as a function of
`x`, but the KAN basis uses positive widths.) -/
theorem continuous_linearBSpline (center width : ℝ) :
    Continuous (linearBSpline center width) := by
  have habs : Continuous (fun x : ℝ => |x - center|) :=
    continuous_abs.comp (continuous_id.sub continuous_const)
  have hratio : Continuous (fun x : ℝ => |x - center| / width) :=
    habs.div_const width
  have hinterior : Continuous (fun x : ℝ => 1 - |x - center| / width) :=
    continuous_const.sub hratio
  simpa [linearBSpline] using continuous_const.max hinterior

/-- Parameters for a finite B-spline KAN specialization. -/
structure LinearBSplineKANData (q : ℕ) where
  parentCenter : Fin q → ℝ
  parentWidth : Fin q → ℝ
  parentWidth_pos : ∀ k, 0 < parentWidth k
  parentScale : Fin q → ℝ
  childCenter : Fin q → ℝ
  childWidth : Fin q → ℝ
  childWidth_pos : ∀ k, 0 < childWidth k
  childScale : Fin q → ℝ
  outer : Fin q → ℝ → ℝ

namespace LinearBSplineKANData

/-- Parent inner coordinate for one KAN channel. -/
def parentInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) (x : ℝ) : ℝ :=
  D.parentScale k * linearBSpline (D.parentCenter k) (D.parentWidth k) x

/-- Child inner coordinate for one KAN channel. -/
def childInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) (x : ℝ) : ℝ :=
  D.childScale k * linearBSpline (D.childCenter k) (D.childWidth k) x

/-- Native specialization into the already-owned finite KAN causal kernel. -/
def toFiniteKANCausalKernel {q : ℕ} (D : LinearBSplineKANData q) :
    FiniteKANCausalKernel q where
  parentInner := D.parentInner
  childInner := D.childInner
  outer := D.outer

/-- Every parent B-spline inner channel is continuous. -/
theorem continuous_parentInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) : Continuous (D.parentInner k) := by
  exact continuous_const.mul
    (continuous_linearBSpline (D.parentCenter k) (D.parentWidth k))

/-- Every child B-spline inner channel is continuous. -/
theorem continuous_childInner {q : ℕ} (D : LinearBSplineKANData q)
    (k : Fin q) : Continuous (D.childInner k) := by
  exact continuous_const.mul
    (continuous_linearBSpline (D.childCenter k) (D.childWidth k))

/-- Parent channel support is compact in the elementary sense that the channel
vanishes once the center-distance is at least its positive width. -/
theorem parentInner_eq_zero_of_outside
    {q : ℕ} (D : LinearBSplineKANData q) (k : Fin q) {x : ℝ}
    (hout : D.parentWidth k ≤ |x - D.parentCenter k|) :
    D.parentInner k x = 0 := by
  simp [parentInner,
    linearBSpline_eq_zero_of_width_le_abs (D.parentWidth_pos k) hout]

/-- Child channel support is compact in the same sense. -/
theorem childInner_eq_zero_of_outside
    {q : ℕ} (D : LinearBSplineKANData q) (k : Fin q) {x : ℝ}
    (hout : D.childWidth k ≤ |x - D.childCenter k|) :
    D.childInner k x = 0 := by
  simp [childInner,
    linearBSpline_eq_zero_of_width_le_abs (D.childWidth_pos k) hout]

/-- The B-spline specialization inherits the hard causal-cone support theorem. -/
theorem cone_of_causal_ne_zero
    {q : ℕ} (D : LinearBSplineKANData q)
    {τParent τChild : ℝ}
    (h : D.toFiniteKANCausalKernel.causal τParent τChild ≠ 0) :
    InForwardLogMassCone τParent τChild := by
  exact FiniteKANCausalKernel.cone_of_causal_ne_zero
    D.toFiniteKANCausalKernel h

end LinearBSplineKANData

end InfoGeometry.MassSpectrometry
