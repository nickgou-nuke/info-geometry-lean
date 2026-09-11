import Mathlib.Analysis.SpecialFunctions.Sqrt
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FierzKleinFoundation
import InfoGeometry.Canonical.RealSpacetime4x4Closure
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Projective.KleinQuadric

set_option autoImplicit false

/-!
# Fierz--Klein--quartic bridge

This module connects the existing Fierz--Klein coordinate surface to the
abstract Freudenthal quartic surface.

The bridge is deliberately explicit:

* Fierz/Klein data comes from
  `InfoGeometry.Canonical.FierzKleinFoundation`;
* the quartic polynomial comes from
  `InfoGeometry.Exceptional.Freudenthal`;
* a user supplies coordinate extraction maps from Fierz--Klein coordinates to a
  Freudenthal charge;
* the final concrete section records a real-spacetime Plücker slice whose Klein
  quadratic readout is the existing `RealSpacetime4x4Closure.interval`, the
  associated interval-square quartic, and an algebraic square-root area
  functional with its degree-two scaling law.

The file proves only compatibility lemmas for those supplied maps.  It does not
construct a spin representation, identify a physical state space, classify
subgroups, prove a causal-boundary theorem, or assert analytic completion.
-/

namespace InfoGeometry.Canonical.FierzKleinQuarticBridge

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Canonical.DrazinModularPersistence
open InfoGeometry.Exceptional.Freudenthal

section Freudenthal

variable {J : Type*}
variable [AddCommGroup J] [Module ℝ J]

/--
A Freudenthal charge assembled from explicit Fierz--Klein coordinate readouts.

The four maps are data, not hidden proof fields:
`alpha`, `beta`, `x`, and `y` say how the chosen Fierz--Klein coordinates are
read as an element of `ℝ ⊕ ℝ ⊕ J ⊕ J`.
-/
@[rep_depth operator]
def fierzKleinCharge
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (X : FierzKleinCoordinates) : FreudenthalCharge J where
  alpha := alpha X
  beta := beta X
  x := x X
  y := y X

/-- Quartic readout obtained by pushing Fierz--Klein coordinates to a Freudenthal charge. -/
@[rep_depth operator]
def quarticReadout
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (X : FierzKleinCoordinates) : ℝ :=
  FreudenthalCharge.quarticInvariant D (fierzKleinCharge alpha beta x y X)

/-- Definitional readback of the quartic bridge. -/
@[rep_depth operator]
theorem quarticReadout_eq_quarticInvariant
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (X : FierzKleinCoordinates) :
    quarticReadout D alpha beta x y X =
      FreudenthalCharge.quarticInvariant D (fierzKleinCharge alpha beta x y X) :=
  rfl

/-- Fierz--Klein coordinates lying on the FK variety and on the quartic divisor. -/
@[rep_depth operator]
def IsFierzKleinQuarticBoundary
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (X : FierzKleinCoordinates) : Prop :=
  IsOnFierzKleinVariety X ∧ quarticReadout D alpha beta x y X = 0

/-- Fierz--Klein coordinates lying on the FK variety and off the quartic divisor. -/
@[rep_depth operator]
def IsFierzKleinQuarticRegular
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (X : FierzKleinCoordinates) : Prop :=
  IsOnFierzKleinVariety X ∧ quarticReadout D alpha beta x y X ≠ 0

/-- Boundary coordinates are, in particular, valid Fierz--Klein coordinates. -/
@[rep_depth operator]
theorem boundary_on_fierzKlein
    {D : CubicJordanDatum J}
    {alpha beta : FierzKleinCoordinates → ℝ}
    {x y : FierzKleinCoordinates → J}
    {X : FierzKleinCoordinates}
    (h : IsFierzKleinQuarticBoundary D alpha beta x y X) :
    IsOnFierzKleinVariety X :=
  h.1

/-- Boundary coordinates have zero quartic readout. -/
@[rep_depth operator]
theorem boundary_quartic_zero
    {D : CubicJordanDatum J}
    {alpha beta : FierzKleinCoordinates → ℝ}
    {x y : FierzKleinCoordinates → J}
    {X : FierzKleinCoordinates}
    (h : IsFierzKleinQuarticBoundary D alpha beta x y X) :
    quarticReadout D alpha beta x y X = 0 :=
  h.2

/-- Regular coordinates are, in particular, valid Fierz--Klein coordinates. -/
@[rep_depth operator]
theorem regular_on_fierzKlein
    {D : CubicJordanDatum J}
    {alpha beta : FierzKleinCoordinates → ℝ}
    {x y : FierzKleinCoordinates → J}
    {X : FierzKleinCoordinates}
    (h : IsFierzKleinQuarticRegular D alpha beta x y X) :
    IsOnFierzKleinVariety X :=
  h.1

/-- Regular coordinates have nonzero quartic readout. -/
@[rep_depth operator]
theorem regular_quartic_ne_zero
    {D : CubicJordanDatum J}
    {alpha beta : FierzKleinCoordinates → ℝ}
    {x y : FierzKleinCoordinates → J}
    {X : FierzKleinCoordinates}
    (h : IsFierzKleinQuarticRegular D alpha beta x y X) :
    quarticReadout D alpha beta x y X ≠ 0 :=
  h.2

/-- The quartic boundary and regular predicates are disjoint. -/
@[rep_depth operator]
theorem boundary_not_regular
    {D : CubicJordanDatum J}
    {alpha beta : FierzKleinCoordinates → ℝ}
    {x y : FierzKleinCoordinates → J}
    {X : FierzKleinCoordinates}
    (hB : IsFierzKleinQuarticBoundary D alpha beta x y X)
    (hR : IsFierzKleinQuarticRegular D alpha beta x y X) :
    False :=
  hR.2 hB.2

/-- Normalized Fierz bilinears enter the quartic boundary once the quartic readout collapses. -/
@[rep_depth operator]
theorem normalized_fierzKlein_quarticBoundary_of_collapse
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (F : FierzBilinears)
    (N : FierzNormalization F)
    (hQ : quarticReadout D alpha beta x y (fierzKleinCoordinates F N) = 0) :
    IsFierzKleinQuarticBoundary D alpha beta x y (fierzKleinCoordinates F N) :=
  ⟨fierzKleinCoordinates_holds F N, hQ⟩

/-- Normalized Fierz bilinears enter the quartic regular sector once the readout is nonzero. -/
@[rep_depth operator]
theorem normalized_fierzKlein_quarticRegular_of_nonzero
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (F : FierzBilinears)
    (N : FierzNormalization F)
    (hQ : quarticReadout D alpha beta x y (fierzKleinCoordinates F N) ≠ 0) :
    IsFierzKleinQuarticRegular D alpha beta x y (fierzKleinCoordinates F N) :=
  ⟨fierzKleinCoordinates_holds F N, hQ⟩

/--
Drazin-horizon Fierz readouts enter the quartic boundary when admissibility and
quartic collapse are supplied explicitly.
-/
@[rep_depth operator]
theorem horizon_fierzKlein_quarticBoundary_of_collapse
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (C : FierzReadoutChannels Obs)
    (S : DrazinSupportData Obs)
    (h : HorizonFierzAdmissible C S)
    (hQ : quarticReadout D alpha beta x y
      (fierzKleinCoordinates (horizonFierzBilinears C S) h.normalization) = 0) :
    IsFierzKleinQuarticBoundary D alpha beta x y
      (fierzKleinCoordinates (horizonFierzBilinears C S) h.normalization) :=
  ⟨horizon_fierz_klein_holds C S h, hQ⟩

/--
Drazin-horizon Fierz readouts enter the quartic regular sector when
admissibility and nonzero quartic readout are supplied explicitly.
-/
@[rep_depth operator]
theorem horizon_fierzKlein_quarticRegular_of_nonzero
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (D : CubicJordanDatum J)
    (alpha beta : FierzKleinCoordinates → ℝ)
    (x y : FierzKleinCoordinates → J)
    (C : FierzReadoutChannels Obs)
    (S : DrazinSupportData Obs)
    (h : HorizonFierzAdmissible C S)
    (hQ : quarticReadout D alpha beta x y
      (fierzKleinCoordinates (horizonFierzBilinears C S) h.normalization) ≠ 0) :
    IsFierzKleinQuarticRegular D alpha beta x y
      (fierzKleinCoordinates (horizonFierzBilinears C S) h.normalization) :=
  ⟨horizon_fierz_klein_holds C S h, hQ⟩

end Freudenthal

/-! ## Concrete real-spacetime interval-square quartic -/

/--
Coordinate Plücker slice associated to a real spacetime coordinate packet.

The signs are chosen so that the existing Klein quadratic form reads back the
`(+---)` Minkowski interval exactly.
-/
@[rep_depth operator]
def spacetimeToPlucker
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    _root_.InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ where
  p01 := X.t + X.z
  p02 := X.x
  p03 := -X.y
  p12 := X.y
  p13 := X.x
  p23 := X.t - X.z

/-- Concrete quartic obtained as the square of the real spacetime interval. -/
@[rep_depth operator]
def spacetimeIntervalQuartic
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) : ℝ :=
  (_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X) ^ 2

/-- The chosen Plücker slice reads back the Minkowski interval through the Klein form. -/
@[rep_depth operator]
theorem spacetimeToPlucker_kleinQ_eq_interval
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    _root_.InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ (spacetimeToPlucker X) =
      _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X := by
  unfold spacetimeToPlucker _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
    _root_.InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ
  ring

/-- The concrete interval quartic is homogeneous of degree four under uniform scaling. -/
@[rep_depth operator]
theorem spacetimeIntervalQuartic_smul
    (c : ℝ) (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    spacetimeIntervalQuartic (_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.smul c X) =
      c ^ 4 * spacetimeIntervalQuartic X := by
  unfold spacetimeIntervalQuartic
  rw [_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval_smul]
  ring

/-- The concrete interval quartic vanishes on the null cone. -/
@[rep_depth operator]
theorem spacetimeIntervalQuartic_eq_zero_of_interval_zero
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (h : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0) :
    spacetimeIntervalQuartic X = 0 := by
  unfold spacetimeIntervalQuartic
  rw [h]
  ring

/-- The concrete interval quartic is the square of the Klein readout on this Plücker slice. -/
@[rep_depth operator]
theorem spacetimeIntervalQuartic_eq_kleinQ_sq
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    spacetimeIntervalQuartic X =
      (_root_.InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ (spacetimeToPlucker X)) ^ 2 := by
  unfold spacetimeIntervalQuartic
  rw [spacetimeToPlucker_kleinQ_eq_interval]

/--
Algebraic entropy-style readout for the concrete spacetime slice.

This is only the real expression `π * sqrt(spacetimeIntervalQuartic X)`; no
black-hole horizon, area theorem, or physical entropy interpretation is asserted
here.
-/
@[rep_depth operator]
noncomputable def spacetimeQuarticEntropyReadout
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) : ℝ :=
  Real.pi * Real.sqrt (spacetimeIntervalQuartic X)

/-- On this slice, the entropy readout is `π · |interval|`. -/
@[rep_depth operator]
theorem spacetimeQuarticEntropyReadout_eq_pi_mul_abs_interval
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    spacetimeQuarticEntropyReadout X = Real.pi * |_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X| := by
  unfold spacetimeQuarticEntropyReadout spacetimeIntervalQuartic
  rw [Real.sqrt_sq_eq_abs]

/-- The algebraic entropy-style readout scales quadratically under uniform scaling. -/
@[rep_depth operator]
theorem spacetimeQuarticEntropyReadout_smul
    (c : ℝ) (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    spacetimeQuarticEntropyReadout (_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.smul c X) =
      c ^ 2 * spacetimeQuarticEntropyReadout X := by
  unfold spacetimeQuarticEntropyReadout
  rw [spacetimeIntervalQuartic_smul]
  rw [Real.sqrt_mul (by positivity)]
  have hsqrt : Real.sqrt (c ^ 4) = c ^ 2 := by
    have hpow : c ^ 4 = (c ^ 2) ^ 2 := by ring
    rw [hpow, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  ring

/-- The same coordinate slice, now in the Fierz--Klein foundation bivector type. -/
@[rep_depth operator]
def spacetimeToFierzBivector
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    Bivector4 where
  p01 := X.t + X.z
  p02 := X.x
  p03 := -X.y
  p12 := X.y
  p13 := X.x
  p23 := X.t - X.z

/-- The Fierz--Klein foundation Klein form reads back the real spacetime interval. -/
@[rep_depth operator]
theorem spacetimeToFierzBivector_kleinForm_eq_interval
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    kleinForm (spacetimeToFierzBivector X) =
      _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X := by
  unfold spacetimeToFierzBivector kleinForm
  unfold _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval
  ring

/-- Fixed normalized scalar-phase coordinate used for the concrete spacetime slice. -/
@[rep_depth operator]
def unitScalarPhase : ScalarPhaseFierz where
  s_hat := 1
  omega_hat := 0

/-- The fixed scalar-phase coordinate lies on the scalar Fierz quadric. -/
@[rep_depth operator]
theorem unitScalarPhase_on_quadric :
    IsOnScalarPhaseFierzQuadric unitScalarPhase := by
  unfold IsOnScalarPhaseFierzQuadric unitScalarPhase
  norm_num

/-- Concrete Fierz--Klein coordinates attached to a real spacetime coordinate packet. -/
@[rep_depth operator]
def spacetimeFierzKleinCoordinates
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    FierzKleinCoordinates where
  scalarPhase := unitScalarPhase
  plucker := spacetimeToFierzBivector X

/-- A null spacetime coordinate packet maps to the Fierz--Klein variety. -/
@[rep_depth operator]
theorem spacetimeFierzKleinCoordinates_on_variety_of_interval_zero
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (h : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0) :
    IsOnFierzKleinVariety (spacetimeFierzKleinCoordinates X) := by
  constructor
  · exact unitScalarPhase_on_quadric
  · unfold spacetimeFierzKleinCoordinates IsOnKleinQuadric
    rw [spacetimeToFierzBivector_kleinForm_eq_interval, h]

/-- Conversely, this concrete Fierz--Klein coordinate lies on the variety only on the null cone. -/
@[rep_depth operator]
theorem interval_eq_zero_of_spacetimeFierzKleinCoordinates_on_variety
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (h : IsOnFierzKleinVariety (spacetimeFierzKleinCoordinates X)) :
    _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0 := by
  exact (spacetimeToFierzBivector_kleinForm_eq_interval X).symm.trans h.2

/-- For this concrete slice, Fierz--Klein variety membership is exactly nullness. -/
@[rep_depth operator]
theorem spacetimeFierzKleinCoordinates_on_variety_iff_interval_zero
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    IsOnFierzKleinVariety (spacetimeFierzKleinCoordinates X) ↔
      _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0 := by
  constructor
  · exact interval_eq_zero_of_spacetimeFierzKleinCoordinates_on_variety X
  · exact spacetimeFierzKleinCoordinates_on_variety_of_interval_zero X

/-- Concrete boundary predicate for the interval-square quartic on the spacetime slice. -/
@[rep_depth operator]
def IsConcreteSpacetimeFierzKleinQuarticBoundary
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) : Prop :=
  IsOnFierzKleinVariety (spacetimeFierzKleinCoordinates X) ∧
    spacetimeIntervalQuartic X = 0

/-- Nullness gives the concrete interval-square quartic boundary. -/
@[rep_depth operator]
theorem concreteSpacetimeBoundary_of_interval_zero
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (h : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0) :
    IsConcreteSpacetimeFierzKleinQuarticBoundary X :=
  ⟨spacetimeFierzKleinCoordinates_on_variety_of_interval_zero X h,
    spacetimeIntervalQuartic_eq_zero_of_interval_zero X h⟩

/-! ## Algebraic square-root area functional -/

/-- Square-root scaling for a fourth-power factor. -/
@[rep_depth operator]
lemma sqrt_c4_mul (c x : ℝ) :
    Real.sqrt (c ^ 4 * x) = c ^ 2 * Real.sqrt x := by
  have hc2 : 0 ≤ c ^ 2 := by positivity
  have h_mul : c ^ 4 * x = (c ^ 2) ^ 2 * x := by ring
  rw [h_mul]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (c ^ 2) ^ 2)]
  rw [Real.sqrt_sq hc2]

/--
Algebraic area-style functional generated from the concrete interval-square
quartic.

This is only the real function `π * sqrt(spacetimeIntervalQuartic X)`.  It is
not, by itself, a black-hole entropy theorem or a physical horizon-area theorem.
-/
@[rep_depth operator]
noncomputable def intervalQuarticSqrtAreaFunctional
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) : ℝ :=
  Real.pi * Real.sqrt (spacetimeIntervalQuartic X)

/-- The algebraic square-root area functional scales quadratically. -/
@[rep_depth operator]
theorem intervalQuarticSqrtAreaFunctional_smul
    (c : ℝ)
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4) :
    intervalQuarticSqrtAreaFunctional
        (_root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.smul c X) =
      c ^ 2 * intervalQuarticSqrtAreaFunctional X := by
  unfold intervalQuarticSqrtAreaFunctional
  rw [spacetimeIntervalQuartic_smul]
  rw [sqrt_c4_mul c (spacetimeIntervalQuartic X)]
  ring

/-- The algebraic square-root area functional vanishes on the null cone. -/
@[rep_depth operator]
theorem intervalQuarticSqrtAreaFunctional_eq_zero_of_interval_zero
    (X : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.RealSpacetime4x4)
    (h : _root_.InfoGeometry.Canonical.RealSpacetime4x4Closure.interval X = 0) :
    intervalQuarticSqrtAreaFunctional X = 0 := by
  unfold intervalQuarticSqrtAreaFunctional
  rw [spacetimeIntervalQuartic_eq_zero_of_interval_zero X h]
  simp

end InfoGeometry.Canonical.FierzKleinQuarticBridge
