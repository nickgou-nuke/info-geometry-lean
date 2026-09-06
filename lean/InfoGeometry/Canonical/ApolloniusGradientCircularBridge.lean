import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Krein.DoubledSpace

/-!
# Apollonius gradient and circular differential geometry

This file gives a branch-independent real-coordinate owner for the differential
geometry of the Cayley/Apollonius potential

`eta(x,y) = log |(x+iy)/(1-x-iy)|`.

Instead of defining a global argument or principal logarithm, it records the
rational differential of `eta` on the twice-punctured plane.  It proves:

* the metric and circular responses are obtained from one covector by `-I`
  and the quarter-turn `J`;
* those responses are orthogonal;
* on the critical line the metric response is normal and the circular response
  is tangent;
* the bipolar cometric gives the differential of `eta` unit norm away from
  the two punctures.

No global branch of `arg`, geodesic-completeness claim, or Riemann-zero
localization theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusGradientCircularBridge

/-- Real coordinates on the Apollonius plane. -/
abbrev PlanePoint := ℝ × ℝ

/-! ## The canonical real-doubled carrier soldering -/

/-
The Apollonius plane already has the carrier shape used by the canonical
real-doubled Krein space with `E := ℝ`.  We therefore solder its two real
coordinates directly to the physical/ghost pair; no complex scalar carrier is
introduced here.
-/

noncomputable def planePointToDoubled :
    PlanePoint →ₗ[ℝ] InfoGeometry.Krein.DoubledSpace ℝ where
  toFun p := InfoGeometry.Krein.to_doubled p.1 p.2
  map_add' p q := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [Prod.fst_add, Prod.snd_add]
  map_smul' a p := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [smul_eq_mul]

@[simp] theorem planePointToDoubled_apply (p : PlanePoint) :
    planePointToDoubled p = InfoGeometry.Krein.to_doubled p.1 p.2 := rfl

@[simp] theorem planePointToDoubled_fst (p : PlanePoint) :
    InfoGeometry.Krein.fst_L (planePointToDoubled p) = p.1 := by
  rfl

@[simp] theorem planePointToDoubled_snd (p : PlanePoint) :
    InfoGeometry.Krein.snd_L (planePointToDoubled p) = p.2 := by
  rfl

theorem planePointToDoubled_injective :
    Function.Injective planePointToDoubled := by
  intro p q h
  apply Prod.ext
  · have hfst := congrArg (fun v => InfoGeometry.Krein.fst_L v) h
    simpa using hfst
  · have hsnd := congrArg (fun v => InfoGeometry.Krein.snd_L v) h
    simpa using hsnd

/-- Squared Euclidean distance to the source at `0`. -/
def distanceZeroSq (p : PlanePoint) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

/-- Squared Euclidean distance to the sink at `1`. -/
def distanceOneSq (p : PlanePoint) : ℝ :=
  (1 - p.1) ^ 2 + p.2 ^ 2

/-- The branch-independent differential coefficients of
`eta = log |s| - log |1-s|`, written in the Euclidean frame. -/
def etaDifferential (p : PlanePoint) : PlanePoint :=
  (p.1 / distanceZeroSq p + (1 - p.1) / distanceOneSq p,
    p.2 / distanceZeroSq p - p.2 / distanceOneSq p)

/-- Counterclockwise quarter-turn, the standard planar Poisson tensor. -/
def quarterTurn (v : PlanePoint) : PlanePoint :=
  (-v.2, v.1)

/-!
The real Hestenes phase axis is the planar quarter-turn after soldering.  This
is the carrier-level identification used downstream; it does not replace the
real doubled carrier by a complex scalar field.
-/
theorem planePointToDoubled_complex_i (p : PlanePoint) :
    InfoGeometry.Krein.complex_i (planePointToDoubled p) =
      planePointToDoubled (quarterTurn p) := by
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [InfoGeometry.Krein.complex_i, InfoGeometry.Krein.modular_j,
      InfoGeometry.Krein.spectral_epsilon, quarterTurn]

theorem planePointToDoubled_quarterTurn_square (p : PlanePoint) :
    quarterTurn (quarterTurn p) = (-p.1, -p.2) := by
  ext <;> simp [quarterTurn]

theorem planePointToDoubled_complex_i_square (p : PlanePoint) :
    InfoGeometry.Krein.complex_i
        (InfoGeometry.Krein.complex_i (planePointToDoubled p)) =
      -planePointToDoubled p := by
  rw [planePointToDoubled_complex_i, planePointToDoubled_complex_i]
  rw [planePointToDoubled_quarterTurn_square]
  change WithLp.toLp (2 : ENNReal) (-p.1, -p.2) =
    -WithLp.toLp (2 : ENNReal) (p.1, p.2)
  rw [← WithLp.toLp_neg]
  rfl

/-! ## Coordinate-to-carrier readout -/

open InfoGeometry.Apollonius

/-- Real coordinate readout of the punctured complex-plane carrier. -/
def puncturedPlaneToPlanePoint (s : PuncturedPlane) : PlanePoint :=
  (s.1.re, s.1.im)

/-- Canonical real doubled-Krein soldering of a punctured-plane point. -/
def puncturedPlaneToDoubled (s : PuncturedPlane) :
    InfoGeometry.Krein.DoubledSpace ℝ :=
  planePointToDoubled (puncturedPlaneToPlanePoint s)

@[simp] theorem puncturedPlaneToDoubled_fst (s : PuncturedPlane) :
    InfoGeometry.Krein.fst_L (puncturedPlaneToDoubled s) = s.1.re := by
  rfl

@[simp] theorem puncturedPlaneToDoubled_snd (s : PuncturedPlane) :
    InfoGeometry.Krein.snd_L (puncturedPlaneToDoubled s) = s.1.im := by
  rfl

theorem puncturedPlaneToDoubled_injective :
    Function.Injective puncturedPlaneToDoubled := by
  intro s t h
  apply Subtype.ext
  apply Complex.ext
  · have hfst := congrArg (fun v => InfoGeometry.Krein.fst_L v) h
    simpa using hfst
  · have hsnd := congrArg (fun v => InfoGeometry.Krein.snd_L v) h
    simpa using hsnd

theorem eta_zero_iff_soldered_fst_eq_half (s : PuncturedPlane) :
    eta s = 0 ↔
      InfoGeometry.Krein.fst_L (puncturedPlaneToDoubled s) = 1 / 2 := by
  rw [puncturedPlaneToDoubled_fst]
  exact eta_zero_iff_re_eq_half s

/-! On the critical line the principal complex readout has no longitudinal
component: it is exactly the imaginary phase component.  The statement is
branch-safe because `theta` remains the existing principal-angle owner. -/
theorem complexPotential_on_criticalLine
    (s : PuncturedPlane) (hline : s.1.re = 1 / 2) :
    complexPotential s = Complex.I * (theta s : ℂ) := by
  rw [complexPotential, (eta_zero_iff_re_eq_half s).2 hline]
  simp

/-- Euclidean pairing used for the finite two-dimensional readout. -/
def pairing (u v : PlanePoint) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Metric/Onsager response generated by the single scalar covector `d eta`. -/
def gradientResponse (p : PlanePoint) : PlanePoint :=
  (-(etaDifferential p).1, -(etaDifferential p).2)

/-- Circular/Poisson response generated from the same covector by `J`. -/
def circularResponse (p : PlanePoint) : PlanePoint :=
  quarterTurn (etaDifferential p)

/-- Every planar covector is orthogonal to its quarter-turn. -/
@[simp] theorem pairing_quarterTurn_self (v : PlanePoint) :
    pairing v (quarterTurn v) = 0 := by
  simp [pairing, quarterTurn]
  ring

/-- The quarter-turn preserves the Euclidean quadratic energy. -/
@[simp] theorem pairing_quarterTurn_quarterTurn (v : PlanePoint) :
    pairing (quarterTurn v) (quarterTurn v) = pairing v v := by
  simp [pairing, quarterTurn]
  ring

/-- The metric and circular Apollonius responses are orthogonal everywhere
that their rational formulas are evaluated. -/
theorem gradientResponse_pairing_circularResponse (p : PlanePoint) :
    pairing (gradientResponse p) (circularResponse p) = 0 := by
  simp [gradientResponse, circularResponse, pairing, quarterTurn]
  ring

/-- The metric and circular responses carry the same Euclidean quadratic
energy, since the circular response is the quarter-turn of the same
Apollonius differential. -/
theorem gradientResponse_energy_eq_circularResponse_energy (p : PlanePoint) :
    pairing (gradientResponse p) (gradientResponse p) =
      pairing (circularResponse p) (circularResponse p) := by
  simp [gradientResponse, circularResponse, pairing, quarterTurn]
  ring

/-- The positive boundary denominator `1/4 + y^2`. -/
def criticalRadiusSq (y : ℝ) : ℝ :=
  (1 / 4 : ℝ) + y ^ 2

theorem criticalRadiusSq_pos (y : ℝ) :
    0 < criticalRadiusSq y := by
  dsimp [criticalRadiusSq]
  nlinarith [sq_nonneg y]

theorem criticalRadiusSq_ne_zero (y : ℝ) :
    criticalRadiusSq y ≠ 0 :=
  ne_of_gt (criticalRadiusSq_pos y)

/-- On `x=1/2`, the differential of `eta` is purely normal and nonzero. -/
theorem etaDifferential_criticalLine (y : ℝ) :
    etaDifferential ((1 / 2 : ℝ), y) =
      ((criticalRadiusSq y)⁻¹, 0) := by
  apply Prod.ext
  · change
      (1 / 2 : ℝ) / ((1 / 2 : ℝ) ^ 2 + y ^ 2) +
          (1 - (1 / 2 : ℝ)) /
            ((1 - (1 / 2 : ℝ)) ^ 2 + y ^ 2) =
        (criticalRadiusSq y)⁻¹
    rw [show ((1 / 2 : ℝ) ^ 2 + y ^ 2) = criticalRadiusSq y by
      simp [criticalRadiusSq]; ring]
    rw [show ((1 - (1 / 2 : ℝ)) ^ 2 + y ^ 2) = criticalRadiusSq y by
      simp [criticalRadiusSq]; ring]
    field_simp [criticalRadiusSq_ne_zero y]
    norm_num
  · change
      y / ((1 / 2 : ℝ) ^ 2 + y ^ 2) -
          y / ((1 - (1 / 2 : ℝ)) ^ 2 + y ^ 2) = 0
    rw [show ((1 / 2 : ℝ) ^ 2 + y ^ 2) =
        ((1 - (1 / 2 : ℝ)) ^ 2 + y ^ 2) by ring]
    ring

/-- The dissipative response is normal to the critical line; it does not
vanish there. -/
theorem gradientResponse_criticalLine (y : ℝ) :
    gradientResponse ((1 / 2 : ℝ), y) =
      (-(criticalRadiusSq y)⁻¹, 0) := by
  rw [gradientResponse, etaDifferential_criticalLine]
  simp

/-- The circular response is tangent to the critical line. -/
theorem circularResponse_criticalLine (y : ℝ) :
    circularResponse ((1 / 2 : ℝ), y) =
      (0, (criticalRadiusSq y)⁻¹) := by
  rw [circularResponse, etaDifferential_criticalLine]
  change (-(0 : ℝ), (criticalRadiusSq y)⁻¹) =
    (0, (criticalRadiusSq y)⁻¹)
  norm_num

/-- The normal metric response never vanishes on the critical line. -/
theorem gradientResponse_criticalLine_ne_zero (y : ℝ) :
    gradientResponse ((1 / 2 : ℝ), y) ≠ 0 := by
  rw [gradientResponse_criticalLine]
  have hfirst : (-(criticalRadiusSq y)⁻¹ : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (criticalRadiusSq_ne_zero y))
  intro h
  exact hfirst (by simpa using congrArg Prod.fst h)

/-- Squared norm of a covector for the inverse bipolar metric
`g^{-1} = |s|^2 |1-s|^2 I`. -/
def bipolarCometricNormSq (p : PlanePoint) (α : PlanePoint) : ℝ :=
  distanceZeroSq p * distanceOneSq p *
    (α.1 ^ 2 + α.2 ^ 2)

/-- The Apollonius logarithmic differential has unit norm in the bipolar
metric, away from the source and sink. -/
theorem bipolarCometricNormSq_etaDifferential
    (p : PlanePoint)
    (h0 : distanceZeroSq p ≠ 0)
    (h1 : distanceOneSq p ≠ 0) :
    bipolarCometricNormSq p (etaDifferential p) = 1 := by
  rcases p with ⟨x, y⟩
  dsimp [bipolarCometricNormSq, etaDifferential,
    distanceZeroSq, distanceOneSq] at h0 h1 ⊢
  field_simp [h0, h1]
  ring

/-! The metric response is the negative of the same covector.  Thus the
cometric norm is unchanged by the sign convention used for the dissipative
flow.  This is the finite carrier statement behind the physical claim that
the Onsager/gradient channel changes orientation, not its normalized scale. -/
theorem bipolarCometricNormSq_gradientResponse
    (p : PlanePoint)
    (h0 : distanceZeroSq p ≠ 0)
    (h1 : distanceOneSq p ≠ 0) :
    bipolarCometricNormSq p (gradientResponse p) = 1 := by
  rw [gradientResponse]
  simpa [bipolarCometricNormSq] using
    (bipolarCometricNormSq_etaDifferential p h0 h1)

end InfoGeometry.Canonical.ApolloniusGradientCircularBridge
