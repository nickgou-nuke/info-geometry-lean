import Mathlib
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetryBase
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.ZetaDihedral

/-!
# InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

This file formalizes the coordinate algebra behind the standard zeta-plane
symmetries.

The point is deliberately structural: the number `1 / 2` appears as the fixed
locus of the chosen affine chart for the antiunitary reflection
`s ↦ 1 - conj s`.  The invariant content is the involutive symmetry frame and
the orbit closure it imposes on any zero predicate stable under the functional
reflection and complex conjugation.

No analytic zeta function is constructed here, and no Riemann-hypothesis claim
is made.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaCoordinateSymmetry

open Complex
open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-! ## Affine chart for the zeta plane -/

/-- Real affine chart for a complex spectral parameter `s = σ + iτ`. -/
structure ZetaAffineChart where
  sigma : ℝ
  tau : ℝ
  deriving DecidableEq

namespace ZetaAffineChart

@[ext] theorem ext {z w : ZetaAffineChart}
    (hsigma : z.sigma = w.sigma) (htau : z.tau = w.tau) : z = w := by
  cases z
  cases w
  simp_all

/-- Convert the real affine chart `(σ, τ)` to the complex parameter `σ + iτ`. -/
def toComplex (z : ZetaAffineChart) : ℂ :=
  ⟨z.sigma, z.tau⟩

/-- Read a complex parameter in the real affine chart. -/
def ofComplex (s : ℂ) : ZetaAffineChart :=
  ⟨s.re, s.im⟩

@[simp] theorem toComplex_re (z : ZetaAffineChart) :
    (z.toComplex).re = z.sigma := rfl

@[simp] theorem toComplex_im (z : ZetaAffineChart) :
    (z.toComplex).im = z.tau := rfl

@[simp] theorem ofComplex_toComplex (z : ZetaAffineChart) :
    ofComplex z.toComplex = z := by
  cases z
  rfl

@[simp] theorem toComplex_ofComplex (s : ℂ) :
    (ofComplex s).toComplex = s := by
  apply Complex.ext <;> rfl

/-! ## The three concrete reflections -/

/-- Complex conjugation in affine coordinates: `(σ, τ) ↦ (σ, -τ)`. -/
def chartConjugation (z : ZetaAffineChart) : ZetaAffineChart :=
  ⟨z.sigma, -z.tau⟩

/-- Functional-equation duality in affine coordinates: `(σ, τ) ↦ (1 - σ, -τ)`. -/
def chartFunctionalDual (z : ZetaAffineChart) : ZetaAffineChart :=
  ⟨1 - z.sigma, -z.tau⟩

/-- Critical antiunitary mirror in affine coordinates: `(σ, τ) ↦ (1 - σ, τ)`. -/
def chartCriticalMirror (z : ZetaAffineChart) : ZetaAffineChart :=
  ⟨1 - z.sigma, z.tau⟩

/-- Centered coordinate `u = σ - 1/2`; the critical line is `u = 0`. -/
def centeredSigma (z : ZetaAffineChart) : ℝ :=
  z.sigma - (1 / 2 : ℝ)

/-- Critical line in the affine chart. -/
def chartCriticalLine (z : ZetaAffineChart) : Prop :=
  z.sigma = (1 / 2 : ℝ)

@[simp] theorem chartConjugation_involutive :
    Function.Involutive chartConjugation := by
  intro z
  ext <;> simp [chartConjugation]

@[simp] theorem chartFunctionalDual_involutive :
    Function.Involutive chartFunctionalDual := by
  intro z
  ext <;> simp [chartFunctionalDual]

@[simp] theorem chartCriticalMirror_involutive :
    Function.Involutive chartCriticalMirror := by
  intro z
  ext <;> simp [chartCriticalMirror]

/-- Functional reflection and conjugation commute in this affine chart. -/
theorem chartFunctional_conjugation_commute (z : ZetaAffineChart) :
    chartFunctionalDual (chartConjugation z) =
      chartConjugation (chartFunctionalDual z) := by
  cases z
  rfl

/-- The antiunitary critical mirror is the composite of functional duality and conjugation. -/
theorem chartCriticalMirror_eq_functional_conjugation (z : ZetaAffineChart) :
    chartCriticalMirror z = chartFunctionalDual (chartConjugation z) := by
  ext <;> simp [chartCriticalMirror, chartFunctionalDual, chartConjugation]

/-- In complex coordinates, chart conjugation is `s ↦ conj s`. -/
theorem toComplex_chartConjugation (z : ZetaAffineChart) :
    (chartConjugation z).toComplex = conjugationReflection z.toComplex := by
  apply Complex.ext <;> simp [toComplex, chartConjugation, conjugationReflection]

/-- In complex coordinates, chart functional duality is `s ↦ 1 - s`. -/
theorem toComplex_chartFunctionalDual (z : ZetaAffineChart) :
    (chartFunctionalDual z).toComplex = functionalReflection z.toComplex := by
  apply Complex.ext <;> simp [toComplex, chartFunctionalDual, functionalReflection]

/-- In complex coordinates, the chart critical mirror is `s ↦ 1 - conj s`. -/
theorem toComplex_chartCriticalMirror (z : ZetaAffineChart) :
    (chartCriticalMirror z).toComplex =
      antiunitaryCriticalReflection z.toComplex := by
  apply Complex.ext <;> simp [toComplex, chartCriticalMirror, antiunitaryCriticalReflection]

/-! ## Fixed locus and centered coordinate -/

/-- The fixed locus of the antiunitary mirror is exactly `σ = 1 / 2`. -/
theorem fixed_chartCriticalMirror_iff_criticalLine (z : ZetaAffineChart) :
    chartCriticalMirror z = z ↔ chartCriticalLine z := by
  constructor
  · intro h
    have hsigma := congrArg ZetaAffineChart.sigma h
    simp [chartCriticalMirror, chartCriticalLine] at hsigma ⊢
    linarith
  · intro h
    ext <;> simp [chartCriticalMirror, chartCriticalLine] at h ⊢
    linarith

/-- The affine critical-line predicate agrees with the complex one. -/
theorem chartCriticalLine_iff_complexCriticalLine (z : ZetaAffineChart) :
    chartCriticalLine z ↔ CriticalLine z.toComplex := by
  rfl

/-- Functional duality negates both centered real coordinate and height. -/
theorem centeredSigma_chartFunctionalDual (z : ZetaAffineChart) :
    centeredSigma (chartFunctionalDual z) = -centeredSigma z := by
  simp [centeredSigma, chartFunctionalDual]
  ring

/-- The antiunitary mirror negates the centered real coordinate and preserves height. -/
theorem centeredSigma_chartCriticalMirror (z : ZetaAffineChart) :
    centeredSigma (chartCriticalMirror z) = -centeredSigma z := by
  simp [centeredSigma, chartCriticalMirror]
  ring

/-- Conjugation preserves the centered real coordinate. -/
theorem centeredSigma_chartConjugation (z : ZetaAffineChart) :
    centeredSigma (chartConjugation z) = centeredSigma z := by
  rfl

/-- The critical line is the zero locus of the centered coordinate. -/
theorem chartCriticalLine_iff_centeredSigma_eq_zero (z : ZetaAffineChart) :
    chartCriticalLine z ↔ centeredSigma z = 0 := by
  unfold chartCriticalLine centeredSigma
  constructor <;> intro h <;> linarith

/-! ## Marked affine pair and scale-normalized midpoint -/

/--
Reflection of a real affine coordinate across the midpoint of a marked pair
`a, b`.

For the standard zeta coordinate the marked real positions are the completed
zeta pole pair `0` and `1`, so this specializes to `σ ↦ 1 - σ`.
-/
def markedPairReflection (a b x : ℝ) : ℝ :=
  a + b - x

/-- Midpoint of the marked affine pair. -/
def markedPairMidpoint (a b : ℝ) : ℝ :=
  (a + b) / 2

/--
Scale-normalized affine coordinate determined by the marked pair.

This sends `a` to `0` and `b` to `1` when `a ≠ b`.
-/
def markedPairScaleCoordinate (a b x : ℝ) : ℝ :=
  (x - a) / (b - a)

/-- Real affine coordinate transport `x ↦ αx + β`. -/
def affineTransport (α β x : ℝ) : ℝ :=
  α * x + β

@[simp] theorem markedPairReflection_left (a b : ℝ) :
    markedPairReflection a b a = b := by
  simp [markedPairReflection]

@[simp] theorem markedPairReflection_right (a b : ℝ) :
    markedPairReflection a b b = a := by
  simp [markedPairReflection]

@[simp] theorem markedPairReflection_involutive (a b : ℝ) :
    Function.Involutive (markedPairReflection a b) := by
  intro x
  simp [markedPairReflection]

/--
The fixed point of the marked-pair reflection is the midpoint.

This is the coordinate-free content behind the standard `1 / 2`: once the
distinguished pair has been normalized to `0, 1`, its midpoint has coordinate
`1 / 2`.
-/
theorem fixed_markedPairReflection_iff_midpoint (a b x : ℝ) :
    markedPairReflection a b x = x ↔ x = markedPairMidpoint a b := by
  constructor
  · intro h
    simp [markedPairReflection, markedPairMidpoint] at h ⊢
    linarith
  · intro h
    simp [markedPairReflection, markedPairMidpoint] at h ⊢
    linarith

@[simp] theorem markedPairScaleCoordinate_left {a b : ℝ} (h : b ≠ a) :
    markedPairScaleCoordinate a b a = 0 := by
  unfold markedPairScaleCoordinate
  field_simp [sub_ne_zero.mpr h]
  ring

@[simp] theorem markedPairScaleCoordinate_right {a b : ℝ} (h : b ≠ a) :
    markedPairScaleCoordinate a b b = 1 := by
  unfold markedPairScaleCoordinate
  field_simp [sub_ne_zero.mpr h]

/-- The marked-pair midpoint has normalized coordinate `1 / 2`. -/
theorem markedPairScaleCoordinate_midpoint {a b : ℝ} (h : b ≠ a) :
    markedPairScaleCoordinate a b (markedPairMidpoint a b) = (1 / 2 : ℝ) := by
  unfold markedPairScaleCoordinate markedPairMidpoint
  field_simp [sub_ne_zero.mpr h]
  ring

/--
In the marked-pair scale coordinate, reflection across the midpoint is exactly
`u ↦ 1 - u`.
-/
theorem markedPairScaleCoordinate_reflection {a b x : ℝ} (h : b ≠ a) :
    markedPairScaleCoordinate a b (markedPairReflection a b x) =
      1 - markedPairScaleCoordinate a b x := by
  unfold markedPairScaleCoordinate markedPairReflection
  field_simp [sub_ne_zero.mpr h]
  ring

/-! ### Affine coordinate transport -/

/--
Affine transport sends the midpoint of a marked pair to the midpoint of the
transported marked pair.
-/
theorem affineTransport_markedPairMidpoint (α β a b : ℝ) :
    affineTransport α β (markedPairMidpoint a b) =
      markedPairMidpoint (affineTransport α β a) (affineTransport α β b) := by
  simp [affineTransport, markedPairMidpoint]
  ring

/--
Affine transport conjugates marked-pair reflection to the reflection of the
transported marked pair.
-/
theorem affineTransport_markedPairReflection (α β a b x : ℝ) :
    affineTransport α β (markedPairReflection a b x) =
      markedPairReflection
        (affineTransport α β a)
        (affineTransport α β b)
        (affineTransport α β x) := by
  simp [affineTransport, markedPairReflection]
  ring

/--
The scale-normalized coordinate is invariant under every nondegenerate affine
transport of the marked pair.
-/
theorem markedPairScaleCoordinate_affineTransport
    {α β a b x : ℝ} (hα : α ≠ 0) :
    markedPairScaleCoordinate
        (affineTransport α β a)
        (affineTransport α β b)
        (affineTransport α β x) =
      markedPairScaleCoordinate a b x := by
  by_cases hb : b = a
  · subst b
    simp [markedPairScaleCoordinate, affineTransport]
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hb
    have htrans :
        affineTransport α β b - affineTransport α β a ≠ 0 := by
      have hprod : α * (b - a) ≠ 0 := mul_ne_zero hα hba
      convert hprod using 1
      simp [affineTransport]
      ring
    unfold markedPairScaleCoordinate
    field_simp [hba, htrans]
    simp [affineTransport]
    ring

/--
Consequently, fixedness under the transported reflection is exactly fixedness
under the original reflection, read through the affine coordinate map.
-/
theorem affineTransport_fixed_reflection_iff_midpoint
    {α β a b x : ℝ} (hα : α ≠ 0) :
    markedPairReflection
        (affineTransport α β a)
        (affineTransport α β b)
        (affineTransport α β x) =
        affineTransport α β x
      ↔ x = markedPairMidpoint a b := by
  rw [← affineTransport_markedPairReflection]
  constructor
  · intro h
    have hcancel : markedPairReflection a b x = x := by
      have hsub : α * (markedPairReflection a b x - x) = 0 := by
        unfold affineTransport at h
        linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hα)
    exact (fixed_markedPairReflection_iff_midpoint a b x).mp hcancel
  · intro hx
    have hreflect : markedPairReflection a b x = x :=
      (fixed_markedPairReflection_iff_midpoint a b x).mpr hx
    rw [hreflect]

/-- The standard zeta real chart is the normalization of the marked pair `0, 1`. -/
theorem standard_markedPairReflection_eq_functional_real (x : ℝ) :
    markedPairReflection 0 1 x = 1 - x := by
  simp [markedPairReflection]

@[simp] theorem standard_markedPairMidpoint :
    markedPairMidpoint 0 1 = (1 / 2 : ℝ) := by
  norm_num [markedPairMidpoint]

/-! ## Symmetry-adapted centered coordinates and Cartan projectors -/

/--
Centered zeta coordinates `u = σ - 1/2`, `v = τ`.

In these coordinates the zeta symmetry frame is linear:
* conjugation is `(u, v) ↦ (u, -v)`;
* functional duality is `(u, v) ↦ (-u, -v)`;
* the critical antiunitary mirror is `(u, v) ↦ (-u, v)`.
-/
structure ZetaCenteredChart where
  u : ℝ
  v : ℝ
  deriving DecidableEq

namespace ZetaCenteredChart

@[ext] theorem ext {x y : ZetaCenteredChart}
    (hu : x.u = y.u) (hv : x.v = y.v) : x = y := by
  cases x
  cases y
  simp_all

/-- Zero vector in centered coordinates. -/
def zero : ZetaCenteredChart :=
  ⟨0, 0⟩

/-- Coordinatewise addition. -/
def add (x y : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u + y.u, x.v + y.v⟩

/-- Coordinatewise negation. -/
def neg (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨-x.u, -x.v⟩

/-- Coordinatewise subtraction. -/
def sub (x y : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u - y.u, x.v - y.v⟩

/-- Coordinatewise scalar multiplication. -/
def scale (a : ℝ) (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨a * x.u, a * x.v⟩

/-- Flat centered quadratic form used by the finite symmetry shadow. -/
def flatQuadratic (x : ZetaCenteredChart) : ℝ :=
  x.u ^ 2 + x.v ^ 2

/-- Flat displacement between two centered points. -/
def flatDisplacement (x y : ZetaCenteredChart) : ℝ :=
  (x.u - y.u) ^ 2 + (x.v - y.v) ^ 2

/-- Conjugation in centered coordinates. -/
def conjugation (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u, -x.v⟩

/-- Functional-equation duality in centered coordinates. -/
def functionalDual (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨-x.u, -x.v⟩

/-- Critical antiunitary mirror in centered coordinates. -/
def criticalMirror (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨-x.u, x.v⟩

/-- The tangent/fixed projector for the critical mirror: projection to the critical line. -/
def criticalTangentProjector (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨0, x.v⟩

/-- The normal/anti-fixed projector for the critical mirror: projection to scale offset. -/
def criticalNormalProjector (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u, 0⟩

/-- The fixed projector for conjugation. -/
def conjugationFixedProjector (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u, 0⟩

/-- The anti-fixed projector for conjugation. -/
def conjugationAntiFixedProjector (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨0, x.v⟩

/-- The fixed projector for functional duality `-I`; its fixed subspace is zero. -/
def functionalFixedProjector (_x : ZetaCenteredChart) : ZetaCenteredChart :=
  zero

/-- The anti-fixed projector for functional duality `-I`; it is the identity projector. -/
def functionalAntiFixedProjector (x : ZetaCenteredChart) : ZetaCenteredChart :=
  x

@[simp] theorem conjugation_involutive :
    Function.Involutive conjugation := by
  intro x
  ext <;> simp [conjugation]

@[simp] theorem functionalDual_involutive :
    Function.Involutive functionalDual := by
  intro x
  ext <;> simp [functionalDual]

@[simp] theorem criticalMirror_involutive :
    Function.Involutive criticalMirror := by
  intro x
  ext <;> simp [criticalMirror]

/-- The critical tangent projector is the normalized `+1` projector `(I + J)/2`. -/
theorem criticalTangent_eq_half_sum (x : ZetaCenteredChart) :
    criticalTangentProjector x =
      scale (1 / 2 : ℝ) (add x (criticalMirror x)) := by
  apply ext
  · simp [criticalTangentProjector, scale, add, criticalMirror]
  · simp [criticalTangentProjector, scale, add, criticalMirror]
    ring

/-- The critical normal projector is the normalized `-1` projector `(I - J)/2`. -/
theorem criticalNormal_eq_half_difference (x : ZetaCenteredChart) :
    criticalNormalProjector x =
      scale (1 / 2 : ℝ) (sub x (criticalMirror x)) := by
  apply ext
  · simp [criticalNormalProjector, scale, sub, criticalMirror]
    ring
  · simp [criticalNormalProjector, scale, sub, criticalMirror]

/-- The conjugation fixed projector is `(I + C)/2`. -/
theorem conjugationFixed_eq_half_sum (x : ZetaCenteredChart) :
    conjugationFixedProjector x =
      scale (1 / 2 : ℝ) (add x (conjugation x)) := by
  apply ext
  · simp [conjugationFixedProjector, scale, add, conjugation]
    ring
  · simp [conjugationFixedProjector, scale, add, conjugation]

/-- The conjugation anti-fixed projector is `(I - C)/2`. -/
theorem conjugationAntiFixed_eq_half_difference (x : ZetaCenteredChart) :
    conjugationAntiFixedProjector x =
      scale (1 / 2 : ℝ) (sub x (conjugation x)) := by
  apply ext
  · simp [conjugationAntiFixedProjector, scale, sub, conjugation]
  · simp [conjugationAntiFixedProjector, scale, sub, conjugation]
    ring

/-- Functional duality has zero fixed projector: `(I + F)/2 = 0`. -/
theorem functionalFixed_eq_half_sum (x : ZetaCenteredChart) :
    functionalFixedProjector x =
      scale (1 / 2 : ℝ) (add x (functionalDual x)) := by
  ext <;> simp [functionalFixedProjector, zero, scale, add, functionalDual]

/-- Functional duality has identity anti-fixed projector: `(I - F)/2 = I`. -/
theorem functionalAntiFixed_eq_half_difference (x : ZetaCenteredChart) :
    functionalAntiFixedProjector x =
      scale (1 / 2 : ℝ) (sub x (functionalDual x)) := by
  ext <;> simp [functionalAntiFixedProjector, scale, sub, functionalDual] <;> ring

/-- Critical tangent and normal projectors resolve the centered point. -/
theorem critical_projectors_resolve (x : ZetaCenteredChart) :
    add (criticalTangentProjector x) (criticalNormalProjector x) = x := by
  ext <;> simp [add, criticalTangentProjector, criticalNormalProjector]

/-- Critical tangent projector is idempotent. -/
theorem criticalTangent_idempotent (x : ZetaCenteredChart) :
    criticalTangentProjector (criticalTangentProjector x) = criticalTangentProjector x := by
  rfl

/-- Critical normal projector is idempotent. -/
theorem criticalNormal_idempotent (x : ZetaCenteredChart) :
    criticalNormalProjector (criticalNormalProjector x) = criticalNormalProjector x := by
  rfl

/-- Critical tangent followed by normal vanishes. -/
theorem criticalNormal_after_tangent (x : ZetaCenteredChart) :
    criticalNormalProjector (criticalTangentProjector x) = zero := by
  rfl

/-- Critical normal followed by tangent vanishes. -/
theorem criticalTangent_after_normal (x : ZetaCenteredChart) :
    criticalTangentProjector (criticalNormalProjector x) = zero := by
  rfl

/-- The critical tangent component is fixed by the critical mirror. -/
theorem criticalMirror_fixes_tangent (x : ZetaCenteredChart) :
    criticalMirror (criticalTangentProjector x) = criticalTangentProjector x := by
  ext <;> simp [criticalMirror, criticalTangentProjector]

/-- The critical normal component is anti-fixed by the critical mirror. -/
theorem criticalMirror_negates_normal (x : ZetaCenteredChart) :
    criticalMirror (criticalNormalProjector x) =
      neg (criticalNormalProjector x) := by
  ext <;> simp [criticalMirror, criticalNormalProjector, neg]

/-- Conjugation preserves the flat centered quadratic form. -/
theorem conjugation_preserves_flatQuadratic (x : ZetaCenteredChart) :
    flatQuadratic (conjugation x) = flatQuadratic x := by
  simp [flatQuadratic, conjugation]

/-- Functional duality preserves the flat centered quadratic form. -/
theorem functionalDual_preserves_flatQuadratic (x : ZetaCenteredChart) :
    flatQuadratic (functionalDual x) = flatQuadratic x := by
  simp [flatQuadratic, functionalDual]

/-- The critical mirror preserves the flat centered quadratic form. -/
theorem criticalMirror_preserves_flatQuadratic (x : ZetaCenteredChart) :
    flatQuadratic (criticalMirror x) = flatQuadratic x := by
  simp [flatQuadratic, criticalMirror]

/-! ## Symmetry potentials and the fixed surface -/

/--
A potential is invariant under the critical mirror when it is even in the
normal coordinate to the critical line.
-/
def CriticalMirrorInvariantPotential (Φ : ZetaCenteredChart → ℝ) : Prop :=
  ∀ x, Φ (criticalMirror x) = Φ x

/--
Reflection invariance forces equal potential values on opposite normal
displacements from the fixed critical surface.

This is the finite algebraic content of "the symmetry surface is a turning
surface"; it does not assert minimum or maximum behavior.
-/
theorem invariantPotential_opposite_normal_values
    {Φ : ZetaCenteredChart → ℝ}
    (hΦ : CriticalMirrorInvariantPotential Φ)
    (u v : ℝ) :
    Φ ⟨-u, v⟩ = Φ ⟨u, v⟩ := by
  simpa [CriticalMirrorInvariantPotential, criticalMirror] using hΦ ⟨u, v⟩

/-- The quadratic symmetry potential drops to the tangent projection by `u²`. -/
theorem flatQuadratic_eq_tangent_plus_normal_sq (x : ZetaCenteredChart) :
    flatQuadratic x =
      flatQuadratic (criticalTangentProjector x) + x.u ^ 2 := by
  simp [flatQuadratic, criticalTangentProjector]
  ring

/--
The fixed critical line minimizes the explicit flat quadratic potential along
the normal direction.
-/
theorem flatQuadratic_tangent_le (x : ZetaCenteredChart) :
    flatQuadratic (criticalTangentProjector x) ≤ flatQuadratic x := by
  rw [flatQuadratic_eq_tangent_plus_normal_sq x]
  exact le_add_of_nonneg_right (sq_nonneg x.u)

/--
For the negative quadratic potential, the same fixed surface is a maximum
along the normal direction.
-/
theorem neg_flatQuadratic_le_tangent (x : ZetaCenteredChart) :
    -flatQuadratic x ≤ -flatQuadratic (criticalTangentProjector x) := by
  exact neg_le_neg (flatQuadratic_tangent_le x)

/--
Normal quadratic potential for the critical mirror.

This is the Souriau-style Hamiltonian attached to displacement away from the
fixed surface in the finite coordinate model.
-/
def normalQuadraticPotential (x : ZetaCenteredChart) : ℝ :=
  x.u ^ 2

/-- The normal quadratic potential is invariant under the critical mirror. -/
theorem normalQuadraticPotential_criticalMirror (x : ZetaCenteredChart) :
    normalQuadraticPotential (criticalMirror x) = normalQuadraticPotential x := by
  simp [normalQuadraticPotential, criticalMirror]

/-- The normal quadratic potential vanishes exactly on the fixed critical surface. -/
theorem normalQuadraticPotential_eq_zero_iff (x : ZetaCenteredChart) :
    normalQuadraticPotential x = 0 ↔ x.u = 0 := by
  simp [normalQuadraticPotential]

/-- Height translation in centered coordinates; infinitesimally this is the vertical field. -/
def heightTranslation (a : ℝ) (x : ZetaCenteredChart) : ZetaCenteredChart :=
  ⟨x.u, x.v + a⟩

/-- Height translations preserve the critical normal/scale coordinate. -/
theorem heightTranslation_preserves_u (a : ℝ) (x : ZetaCenteredChart) :
    (heightTranslation a x).u = x.u := rfl

/-- Height translations preserve the critical-line predicate `u = 0`. -/
theorem heightTranslation_preserves_criticalLine (a : ℝ) (x : ZetaCenteredChart) :
    x.u = 0 → (heightTranslation a x).u = 0 := by
  intro h
  exact h

/-- The critical mirror commutes with height translations. -/
theorem criticalMirror_commutes_heightTranslation (a : ℝ) (x : ZetaCenteredChart) :
    criticalMirror (heightTranslation a x) =
      heightTranslation a (criticalMirror x) := by
  rfl

/--
Height translation preserves flat displacement.  This is the algebraic
finite-dimensional shadow of the vertical Killing field in the centered chart.
-/
theorem heightTranslation_preserves_flatDisplacement
    (a : ℝ) (x y : ZetaCenteredChart) :
    flatDisplacement (heightTranslation a x) (heightTranslation a y) =
      flatDisplacement x y := by
  simp [flatDisplacement, heightTranslation]

/-- Height translations compose by addition of their parameters. -/
theorem heightTranslation_add (a b : ℝ) (x : ZetaCenteredChart) :
    heightTranslation a (heightTranslation b x) =
      heightTranslation (a + b) x := by
  ext <;> simp [heightTranslation]
  ring

@[simp] theorem heightTranslation_zero (x : ZetaCenteredChart) :
    heightTranslation 0 x = x := by
  ext <;> simp [heightTranslation]

/--
The coordinate-frame height moment.

This is not a completed-zeta analytic moment map. It is the finite Souriau
readout for the vertical translation extension of the centered chart.
-/
def heightSouriauMoment (x : ZetaCenteredChart) : ℝ :=
  x.v

/-- The height-flow Souriau cocycle is the translation parameter. -/
def heightSouriauCocycle (a : ℝ) : ℝ :=
  a

/--
The height moment is equivariant up to the Souriau cocycle for vertical
translations.
-/
theorem heightSouriauMoment_equivariance (a : ℝ) (x : ZetaCenteredChart) :
    heightSouriauMoment (heightTranslation a x) =
      heightSouriauMoment x + heightSouriauCocycle a := by
  simp [heightSouriauMoment, heightSouriauCocycle, heightTranslation]

/-- The normal quadratic potential is invariant under the height-flow extension. -/
theorem normalQuadraticPotential_heightTranslation (a : ℝ) (x : ZetaCenteredChart) :
    normalQuadraticPotential (heightTranslation a x) =
      normalQuadraticPotential x := by
  rfl

/-- Conjugation reverses the height-translation parameter. -/
theorem conjugation_reverses_heightTranslation (a : ℝ) (x : ZetaCenteredChart) :
    conjugation (heightTranslation a x) =
      heightTranslation (-a) (conjugation x) := by
  ext <;> simp [conjugation, heightTranslation]
  ring

/-- Functional duality also reverses the height-translation parameter. -/
theorem functionalDual_reverses_heightTranslation (a : ℝ) (x : ZetaCenteredChart) :
    functionalDual (heightTranslation a x) =
      heightTranslation (-a) (functionalDual x) := by
  ext <;> simp [functionalDual, heightTranslation]
  ring

end ZetaCenteredChart

/-- Convert from affine zeta coordinates to centered symmetry-adapted coordinates. -/
def toCentered (z : ZetaAffineChart) : ZetaCenteredChart :=
  ⟨centeredSigma z, z.tau⟩

/-- Convert from centered symmetry-adapted coordinates back to affine coordinates. -/
def fromCentered (x : ZetaCenteredChart) : ZetaAffineChart :=
  ⟨x.u + (1 / 2 : ℝ), x.v⟩

@[simp] theorem fromCentered_toCentered (z : ZetaAffineChart) :
    fromCentered (toCentered z) = z := by
  apply ext
  · simp [fromCentered, toCentered, centeredSigma]
  · simp [fromCentered, toCentered, centeredSigma]

@[simp] theorem toCentered_fromCentered (x : ZetaCenteredChart) :
    toCentered (fromCentered x) = x := by
  apply ZetaCenteredChart.ext
  · simp [fromCentered, toCentered, centeredSigma]
  · simp [fromCentered, toCentered, centeredSigma]

theorem toCentered_chartConjugation (z : ZetaAffineChart) :
    toCentered (chartConjugation z) =
      ZetaCenteredChart.conjugation (toCentered z) := by
  ext <;> simp [toCentered, centeredSigma, chartConjugation,
    ZetaCenteredChart.conjugation]

theorem toCentered_chartFunctionalDual (z : ZetaAffineChart) :
    toCentered (chartFunctionalDual z) =
      ZetaCenteredChart.functionalDual (toCentered z) := by
  apply ZetaCenteredChart.ext
  · simp [toCentered, centeredSigma, chartFunctionalDual, ZetaCenteredChart.functionalDual]
    ring
  · simp [toCentered, centeredSigma, chartFunctionalDual, ZetaCenteredChart.functionalDual]

theorem toCentered_chartCriticalMirror (z : ZetaAffineChart) :
    toCentered (chartCriticalMirror z) =
      ZetaCenteredChart.criticalMirror (toCentered z) := by
  apply ZetaCenteredChart.ext
  · simp [toCentered, centeredSigma, chartCriticalMirror, ZetaCenteredChart.criticalMirror]
    ring
  · simp [toCentered, centeredSigma, chartCriticalMirror, ZetaCenteredChart.criticalMirror]

/-! ## The generated finite symmetry frame -/

/--
The four concrete zeta-plane chart symmetries generated by functional duality
and conjugation.  Analytically these are the standard zero-orbit symmetries of
the completed zeta/xi function.
-/
inductive ChartSymmetry where
  | identity
  | conjugation
  | functionalDual
  | criticalMirror
  deriving DecidableEq, Repr

/-- Action of the generated chart symmetry frame. -/
def chartSymmetryAct : ChartSymmetry → ZetaAffineChart → ZetaAffineChart
  | ChartSymmetry.identity, z => z
  | ChartSymmetry.conjugation, z => chartConjugation z
  | ChartSymmetry.functionalDual, z => chartFunctionalDual z
  | ChartSymmetry.criticalMirror, z => chartCriticalMirror z

/-- Composition table for the generated Klein-four symmetry frame. -/
def chartSymmetryCompose : ChartSymmetry → ChartSymmetry → ChartSymmetry
  | ChartSymmetry.identity, h => h
  | g, ChartSymmetry.identity => g
  | ChartSymmetry.conjugation, ChartSymmetry.conjugation =>
      ChartSymmetry.identity
  | ChartSymmetry.functionalDual, ChartSymmetry.functionalDual =>
      ChartSymmetry.identity
  | ChartSymmetry.criticalMirror, ChartSymmetry.criticalMirror =>
      ChartSymmetry.identity
  | ChartSymmetry.conjugation, ChartSymmetry.functionalDual =>
      ChartSymmetry.criticalMirror
  | ChartSymmetry.functionalDual, ChartSymmetry.conjugation =>
      ChartSymmetry.criticalMirror
  | ChartSymmetry.conjugation, ChartSymmetry.criticalMirror =>
      ChartSymmetry.functionalDual
  | ChartSymmetry.criticalMirror, ChartSymmetry.conjugation =>
      ChartSymmetry.functionalDual
  | ChartSymmetry.functionalDual, ChartSymmetry.criticalMirror =>
      ChartSymmetry.conjugation
  | ChartSymmetry.criticalMirror, ChartSymmetry.functionalDual =>
      ChartSymmetry.conjugation

/-- The composition table agrees with function composition of the chart action. -/
theorem chartSymmetryAct_compose (g h : ChartSymmetry) (z : ZetaAffineChart) :
    chartSymmetryAct (chartSymmetryCompose g h) z =
      chartSymmetryAct g (chartSymmetryAct h z) := by
  cases g <;> cases h <;> ext <;>
    simp [chartSymmetryAct, chartSymmetryCompose, chartConjugation,
      chartFunctionalDual, chartCriticalMirror]

/-- Every generated chart symmetry is an involution. -/
theorem chartSymmetryAct_involutive (g : ChartSymmetry) :
    Function.Involutive (chartSymmetryAct g) := by
  intro z
  cases g <;> ext <;>
    simp [chartSymmetryAct, chartConjugation, chartFunctionalDual,
      chartCriticalMirror]

/-- The generated symmetry frame is commutative. -/
theorem chartSymmetryCompose_commute (g h : ChartSymmetry) :
    chartSymmetryCompose g h = chartSymmetryCompose h g := by
  cases g <;> cases h <;> rfl

/-- Each generated symmetry squares to the identity in the composition table. -/
theorem chartSymmetryCompose_self (g : ChartSymmetry) :
    chartSymmetryCompose g g = ChartSymmetry.identity := by
  cases g <;> rfl

/-- All generated chart symmetries preserve the critical line. -/
theorem chartSymmetryAct_preserves_criticalLine
    (g : ChartSymmetry) (z : ZetaAffineChart) :
    chartCriticalLine z → chartCriticalLine (chartSymmetryAct g z) := by
  intro h
  cases g <;>
    simp [chartSymmetryAct, chartCriticalLine, chartConjugation,
      chartFunctionalDual, chartCriticalMirror] at h ⊢ <;>
    linarith

/-! ## Souriau thermodynamics of the finite zeta symmetry group -/

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
The generated completed-zeta chart symmetry frame is finite/discrete. Its
Lean-side infinitesimal Souriau temperature carrier below is therefore the
one-point Lie algebra, and the corresponding finite moment/Massieu readouts are
proved invariant.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None in this section.

#### BUCKET 3: OPEN CLOSURE DEBT
Analytic Souriau thermodynamics for the completed zeta function, coadjoint
orbits, and KMS states are not claimed here.
-/

/--
Infinitesimal temperature carrier for the generated finite zeta symmetry group.

The actual generated `ChartSymmetry` group is finite, hence zero-dimensional as
a Lie group.  The theorem-safe infinitesimal carrier is therefore a singleton.
-/
abbrev DiscreteZetaSouriauTemperature : Type :=
  PUnit

/-- The finite symmetry group acts trivially on its zero-dimensional Lie algebra. -/
def chartSymmetryTemperatureAct (_g : ChartSymmetry)
    (β : DiscreteZetaSouriauTemperature) : DiscreteZetaSouriauTemperature :=
  β

/-- Moment map for the discrete zeta symmetry group: necessarily zero. -/
def discreteZetaSouriauMoment (_β : DiscreteZetaSouriauTemperature) : ℝ :=
  0

/-- Massieu potential for the discrete zeta symmetry group: constant zero. -/
def discreteZetaMassieu (_β : DiscreteZetaSouriauTemperature) : ℝ :=
  0

@[simp] theorem chartSymmetryTemperatureAct_eq
    (g : ChartSymmetry) (β : DiscreteZetaSouriauTemperature) :
    chartSymmetryTemperatureAct g β = β := rfl

/-- The discrete Souriau moment is invariant under every generated zeta symmetry. -/
theorem discreteZetaSouriauMoment_invariant
    (g : ChartSymmetry) (β : DiscreteZetaSouriauTemperature) :
    discreteZetaSouriauMoment (chartSymmetryTemperatureAct g β) =
      discreteZetaSouriauMoment β := by
  rfl

/-- The discrete Massieu potential is invariant under every generated zeta symmetry. -/
theorem discreteZetaMassieu_invariant
    (g : ChartSymmetry) (β : DiscreteZetaSouriauTemperature) :
    discreteZetaMassieu (chartSymmetryTemperatureAct g β) =
      discreteZetaMassieu β := by
  rfl

/--
There is no nontrivial infinitesimal Souriau temperature in the finite generated
zeta symmetry group.
-/
theorem discreteZetaSouriauTemperature_subsingleton :
    Subsingleton DiscreteZetaSouriauTemperature := by
  infer_instance

/-! ## Coordinate-independent zero-orbit closure -/

/--
Abstract zero predicate stable under the two generating zeta-plane symmetries.

For the completed entire xi function this is the usual symmetry package:
if `ρ` is a zero, then so are `conj ρ`, `1 - ρ`, and `1 - conj ρ`.
This structure records only the symmetry closure, not analytic existence of
zeros.
-/
structure ZeroSetSymmetry where
  IsZero : ZetaAffineChart → Prop
  conjugation_preserves :
    ∀ z, IsZero z → IsZero (chartConjugation z)
  functionalDual_preserves :
    ∀ z, IsZero z → IsZero (chartFunctionalDual z)

namespace ZeroSetSymmetry

/-- Closure under the antiunitary critical mirror follows from the two generators. -/
theorem criticalMirror_preserves (Z : ZeroSetSymmetry) (z : ZetaAffineChart)
    (hz : Z.IsZero z) :
    Z.IsZero (chartCriticalMirror z) := by
  rw [chartCriticalMirror_eq_functional_conjugation]
  exact Z.functionalDual_preserves (chartConjugation z)
    (Z.conjugation_preserves z hz)

/-- The four symmetry images generated by conjugation and functional duality. -/
theorem four_point_orbit (Z : ZeroSetSymmetry) (z : ZetaAffineChart)
    (hz : Z.IsZero z) :
    Z.IsZero z ∧
      Z.IsZero (chartConjugation z) ∧
      Z.IsZero (chartFunctionalDual z) ∧
      Z.IsZero (chartCriticalMirror z) := by
  exact ⟨hz,
    Z.conjugation_preserves z hz,
    Z.functionalDual_preserves z hz,
    Z.criticalMirror_preserves z hz⟩

end ZeroSetSymmetry

end ZetaAffineChart

end InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
