import InfoGeometry.Canonical.SplitOctonionColorCycleMultiplicativity
import Mathlib.LinearAlgebra.Basis.Basic

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-! The rational quadratic and trilinear forms transported by the split
octonion coordinates.  This is a finite algebraic `G₂`-invariant witness; it
does not assert a holonomy or gauge-connection theorem. -/

def splitImaginaryPart : Set StandardRationalSplitOctonion :=
  {x | x .one = 0}

def splitInner (x y : StandardRationalSplitOctonion) : ℚ :=
  (coordinateSplitNorm (x + y) - coordinateSplitNorm x - coordinateSplitNorm y) / 2

/-!
## Ambient metric and orientation data

The split-octonion carrier is the ambient eight-dimensional space for the
Zorn/vector model.  The metric below is the polarization of the existing
coordinate norm.  Orientation is represented by the ordered named basis
`IntegralSplitBasis`; no imaginary-part restriction and no new Hodge operator
are introduced here.
-/

/-- The ambient split metric, expressed as a native Mathlib bilinear form. -/
noncomputable def splitOctonionMetric :
    LinearMap.BilinForm ℚ StandardRationalSplitOctonion :=
  LinearMap.mk₂ ℚ splitInner
    (by
      intro x y z
      simp [splitInner, coordinateSplitNorm]
      ring)
    (by
      intro r x y
      simp [splitInner, coordinateSplitNorm]
      ring)
    (by
      intro x y z
      simp [splitInner, coordinateSplitNorm]
      ring)
    (by
      intro r x y
      simp [splitInner, coordinateSplitNorm]
      ring)

@[simp] theorem splitOctonionMetric_apply
    (x y : StandardRationalSplitOctonion) :
    splitOctonionMetric x y = splitInner x y := by
  rfl

theorem splitOctonionMetric_quadratic
    (x : StandardRationalSplitOctonion) :
    splitOctonionMetric x x = coordinateSplitNorm x := by
  simp [splitOctonionMetric, splitInner, coordinateSplitNorm]
  ring

/-!
The following finite readout records the sign convention of the named frame.
In particular, on the imaginary coordinates there are three positive basis
directions (`i`, `j`, `k`) and four negative ones (`l`, `il`, `jl`, `kl`).
This is a coordinate theorem only; it does not by itself assert a general
`HasSignature` instance.
-/
theorem coordinateSplitNorm_single_basis
    (b : IntegralSplitBasis) (q : ℚ) :
    coordinateSplitNorm (Pi.single b q) =
      match b with
      | .one => q ^ 2
      | .l => -q ^ 2
      | .i => q ^ 2
      | .il => -q ^ 2
      | .j => q ^ 2
      | .jl => -q ^ 2
      | .k => q ^ 2
      | .kl => -q ^ 2 := by
  cases b <;> simp [coordinateSplitNorm]

/-- The canonical ordered frame used as orientation data for the ambient carrier. -/
noncomputable def standardSplitOctonionBasis :
    Module.Basis IntegralSplitBasis ℚ StandardRationalSplitOctonion :=
  Pi.basisFun ℚ IntegralSplitBasis

/-- An orientation witness is an ordered Mathlib basis, not an exterior Hodge map. -/
abbrev SplitOctonionOrientation :=
  Module.Basis IntegralSplitBasis ℚ StandardRationalSplitOctonion

/-!
The bundle records exactly the finite data needed before constructing a
degree-reversing Hodge map: an ambient bilinear metric and an oriented frame.
It deliberately does not assert nondegeneracy, a signature theorem, or a
canonical Hodge star.
-/
structure SplitOctonionMetricOrientation where
  metric : LinearMap.BilinForm ℚ StandardRationalSplitOctonion
  orientation : SplitOctonionOrientation
  metric_eq : metric = splitOctonionMetric

noncomputable def standardSplitOctonionMetricOrientation :
    SplitOctonionMetricOrientation :=
  { metric := splitOctonionMetric
    orientation := standardSplitOctonionBasis
    metric_eq := rfl }

@[simp] theorem standardSplitOctonionMetricOrientation_metric :
    standardSplitOctonionMetricOrientation.metric = splitOctonionMetric := by
  simp [standardSplitOctonionMetricOrientation]

@[simp] theorem standardSplitOctonionMetricOrientation_orientation :
    standardSplitOctonionMetricOrientation.orientation =
      standardSplitOctonionBasis := by
  simp [standardSplitOctonionMetricOrientation]

theorem splitOctonionMetric_is_zorn_norm
    (x : StandardRationalSplitOctonion) :
    splitOctonionMetric x x =
      ZornVectorMatrix.norm (zornVectorMatrixRationalEquiv x) := by
  rw [splitOctonionMetric_quadratic]
  exact (zornVectorMatrixRationalEquiv_preserves_norm x).symm

def canonicalThreeForm
    (x y z : StandardRationalSplitOctonion) : ℚ :=
  splitInner (splitOctonionMulQ x y) z

theorem trialityColorCycle_preserves_norm
    (x : StandardRationalSplitOctonion) :
    coordinateSplitNorm (trialityColorCycle x) = coordinateSplitNorm x := by
  simp [coordinateSplitNorm, trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv]
  ring

theorem trialityColorCycle_preserves_inner
    (x y : StandardRationalSplitOctonion) :
    splitInner (trialityColorCycle x) (trialityColorCycle y) =
      splitInner x y := by
  unfold splitInner
  have hsum :
      trialityColorCycle (x + y) =
        trialityColorCycle x + trialityColorCycle y :=
    trialityColorCycle.map_add x y
  rw [← hsum, trialityColorCycle_preserves_norm (x + y),
    trialityColorCycle_preserves_norm x,
    trialityColorCycle_preserves_norm y]

theorem trialityColorCycle_preserves_canonicalThreeForm
    (x y z : StandardRationalSplitOctonion) :
    canonicalThreeForm
        (trialityColorCycle x)
        (trialityColorCycle y)
        (trialityColorCycle z) =
      canonicalThreeForm x y z := by
  unfold canonicalThreeForm
  rw [← trialityColorCycle_map_mul]
  exact trialityColorCycle_preserves_inner (splitOctonionMulQ x y) z

theorem trialityColorCycle_fixes_shared_hyperbolic_axis
    {x : StandardRationalSplitOctonion}
    (hx : x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧
      x .k = 0 ∧ x .kl = 0) :
    trialityColorCycle x = x := by
  funext b
  cases b <;>
    simp [trialityColorCycle, colorCycleBasisEquiv, colorCycleBasis,
      colorCycleBasisInv, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
      hx.2.2.2.2.1, hx.2.2.2.2.2]

end InfoGeometry.Canonical
