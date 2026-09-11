import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Virasoro coadjoint readout of the bipolar projective connection

For a scalar parameter `c`, this file defines the normalized projective
connection

`P_c(s) = -(c/12) S_W(s) = -c / (24 s² (s-1)²)`.

It proves its genuine complex derivative, the algebraic Virasoro coadjoint
compatibility, disappearance of the central term on quadratic projective vector
fields, and the two equal double-pole coefficients `-c/24`.

The coefficient `-c/24` is a double-pole coefficient, not a residue.  The exact
partial-fraction formula also contains simple-pole terms.  A cylinder-vacuum
Casimir interpretation requires a CFT state, coordinate convention, and
central-charge normalization; no such physical data are assumed here.
-/

noncomputable section

namespace InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection

/-- Common denominator of the bipolar quadratic-pole coefficient. -/
def poleDenominator (s : ℂ) : ℂ :=
  s ^ 2 * (s - 1) ^ 2

/-- Derivative of the common denominator. -/
def poleDenominatorDeriv (s : ℂ) : ℂ :=
  2 * s * (s - 1) ^ 2 + 2 * (s - 1) * s ^ 2

/-- Common leading coefficient of the two quadratic poles. -/
def doublePoleCoefficient (c : ℂ) : ℂ :=
  -c / 24

/-- Genuine derivative of the polynomial pole denominator. -/
theorem hasDerivAt_poleDenominator (s : ℂ) :
    HasDerivAt poleDenominator (poleDenominatorDeriv s) s := by
  have h₀ := (hasDerivAt_id s).pow 2
  have h₁ := ((hasDerivAt_id s).sub_const 1).pow 2
  convert h₀.mul h₁ using 1 <;>
    simp [poleDenominator, poleDenominatorDeriv] <;> ring

/-- Normalized projective connection associated with the bipolar logarithmic
Schwarzian. -/
def bipolarProjectiveConnection (c : ℂ) (s : ℂ) : ℂ :=
  doublePoleCoefficient c / poleDenominator s

/-- Rational derivative coefficient of the normalized projective connection. -/
def bipolarProjectiveConnectionDeriv (c : ℂ) (s : ℂ) : ℂ :=
  (c / 12) * (2 * s - 1) / (s ^ 3 * (s - 1) ^ 3)

/-- The projective connection is exactly `-(c/12)` times the logarithmic
Schwarzian on the punctured domain. -/
theorem bipolarProjectiveConnection_eq_schwarzian
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    bipolarProjectiveConnection c s =
      -(c / 12) * bipolarSchwarzian s := by
  rw [bipolarSchwarzian_eq_rational hs]
  unfold bipolarProjectiveConnection doublePoleCoefficient poleDenominator
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  field_simp [h₀, h₁]
  ring

/-- Rational normal form stated without the intermediate Schwarzian name. -/
theorem bipolarProjectiveConnection_eq_rational
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    bipolarProjectiveConnection c s =
      -c / (24 * s ^ 2 * (s - 1) ^ 2) := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold bipolarProjectiveConnection doublePoleCoefficient poleDenominator
  field_simp [h₀, h₁]

/-- Exact square-of-the-logarithmic-form factorization. -/
theorem bipolarProjectiveConnection_eq_dlog01_sq
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    bipolarProjectiveConnection c s =
      -(c / 24) * dlog01 s ^ 2 := by
  rw [bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs]
  ring

/-- Exact partial-fraction decomposition.  In addition to the equal quadratic
pole coefficients, the global rational function contains fixed simple-pole
terms. -/
theorem bipolarProjectiveConnection_partialFractions
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    bipolarProjectiveConnection c s =
      doublePoleCoefficient c / s ^ 2 +
      doublePoleCoefficient c / (s - 1) ^ 2 +
      (2 * doublePoleCoefficient c) / s -
      (2 * doublePoleCoefficient c) / (s - 1) := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold bipolarProjectiveConnection poleDenominator
  field_simp [h₀, h₁]
  ring

/-- Genuine complex derivative of the normalized projective connection away
from its two poles. -/
theorem hasDerivAt_bipolarProjectiveConnection
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt (bipolarProjectiveConnection c)
      (bipolarProjectiveConnectionDeriv c s) s := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have hden : poleDenominator s ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 h₀) (pow_ne_zero 2 h₁)
  have hraw :=
    (hasDerivAt_const s (doublePoleCoefficient c)).div
      (hasDerivAt_poleDenominator s) hden
  change HasDerivAt
    (fun z : ℂ => doublePoleCoefficient c / poleDenominator z)
    (bipolarProjectiveConnectionDeriv c s) s
  convert hraw using 1
  unfold bipolarProjectiveConnectionDeriv doublePoleCoefficient
    poleDenominator poleDenominatorDeriv
  field_simp [h₀, h₁]
  ring

/-- Ordinary derivative readout of the projective connection. -/
theorem deriv_bipolarProjectiveConnection
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    deriv (bipolarProjectiveConnection c) s =
      bipolarProjectiveConnectionDeriv c s := by
  exact (hasDerivAt_bipolarProjectiveConnection c hs).deriv

/-- Derivative of the bare bipolar Schwarzian coefficient. -/
def bipolarSchwarzianDeriv (s : ℂ) : ℂ :=
  bipolarSchwarzianRationalDeriv s

/-- The bare Schwarzian derivative symbol is a genuine derivative. -/
theorem hasDerivAt_bipolarSchwarzian_readout
    {s : ℂ} (hs : s ∈ punctured01) :
    HasDerivAt bipolarSchwarzian (bipolarSchwarzianDeriv s) s := by
  simpa [bipolarSchwarzianDeriv] using
    InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection.hasDerivAt_bipolarSchwarzian hs

/-- Ordinary derivative readout of the bare Schwarzian. -/
theorem deriv_bipolarSchwarzian_readout
    {s : ℂ} (hs : s ∈ punctured01) :
    deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s := by
  exact (hasDerivAt_bipolarSchwarzian_readout hs).deriv

/-- The normalized derivative is `-(c/12)` times the bare Schwarzian derivative. -/
theorem bipolarProjectiveConnectionDeriv_eq_schwarzianDeriv
    (c s : ℂ) :
    bipolarProjectiveConnectionDeriv c s =
      -(c / 12) * bipolarSchwarzianDeriv s := by
  unfold bipolarProjectiveConnectionDeriv bipolarSchwarzianDeriv
    bipolarSchwarzianRationalDeriv
  ring

/-- Chosen infinitesimal projective-connection convention for a Schwarzian
coefficient: `δS = v S' + 2v' S - v'''`. -/
def schwarzianCoadjointVariation
    (S S' v v' v''' : ℂ) : ℂ :=
  v * S' + 2 * v' * S - v'''

/-- Corresponding Virasoro coadjoint variation of a normalized projective
connection: `δP = vP' + 2v'P + (c/12)v'''`. -/
def projectiveConnectionVariation
    (c P P' v v' v''' : ℂ) : ℂ :=
  v * P' + 2 * v' * P + (c / 12) * v'''

/-- Universal algebraic compatibility between the Schwarzian convention and
its `-(c/12)` projective-connection normalization. -/
theorem ward_schwarzian_scaling
    (c S S' v v' v''' : ℂ) :
    -(c / 12) * schwarzianCoadjointVariation S S' v v' v''' =
      projectiveConnectionVariation c
        (-(c / 12) * S) (-(c / 12) * S') v v' v''' := by
  unfold schwarzianCoadjointVariation projectiveConnectionVariation
  ring

/-- Specialized Ward compatibility for the bipolar projective connection.  Both
`S'` and `P'` in this statement are independently certified derivatives. -/
theorem bipolar_ward_schwarzian_compatibility
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (v v' v''' : ℂ) :
    -(c / 12) * schwarzianCoadjointVariation
        (bipolarSchwarzian s) (bipolarSchwarzianDeriv s) v v' v''' =
      projectiveConnectionVariation c
        (bipolarProjectiveConnection c s)
        (bipolarProjectiveConnectionDeriv c s) v v' v''' := by
  rw [bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarProjectiveConnectionDeriv_eq_schwarzianDeriv]
  exact ward_schwarzian_scaling c
    (bipolarSchwarzian s) (bipolarSchwarzianDeriv s) v v' v'''

/-- Holomorphic polynomial vector fields of degree at most two, used only as an
analytic evaluation carrier.  The repository's genuine Witt algebra remains
the algebraic owner of the projective modes. -/
structure ProjectiveVectorField where
  constant : ℂ
  linear : ℂ
  quadratic : ℂ

namespace ProjectiveVectorField

/-- Value of `a + b s + d s²`. -/
def value (v : ProjectiveVectorField) (s : ℂ) : ℂ :=
  v.constant + v.linear * s + v.quadratic * s ^ 2

/-- First derivative of a projective vector field. -/
def first (v : ProjectiveVectorField) (s : ℂ) : ℂ :=
  v.linear + 2 * v.quadratic * s

/-- Second derivative of a projective vector field. -/
def second (v : ProjectiveVectorField) (_s : ℂ) : ℂ :=
  2 * v.quadratic

/-- Third derivative of a projective vector field. -/
def third (_v : ProjectiveVectorField) (_s : ℂ) : ℂ :=
  0

/-- The displayed first derivative is genuine. -/
theorem hasDerivAt_value (v : ProjectiveVectorField) (s : ℂ) :
    HasDerivAt v.value (v.first s) s := by
  have h₀ := hasDerivAt_const s v.constant
  have h₁ := (hasDerivAt_id s).const_mul v.linear
  have h₂ := ((hasDerivAt_id s).pow 2).const_mul v.quadratic
  convert h₀.add (h₁.add h₂) using 1
  · funext z
    dsimp [value]
    ring
  · dsimp [first]
    ring

/-- The displayed second derivative is genuine. -/
theorem hasDerivAt_first (v : ProjectiveVectorField) (s : ℂ) :
    HasDerivAt v.first (v.second s) s := by
  have h₀ := hasDerivAt_const s v.linear
  have h₁ := (hasDerivAt_id s).const_mul (2 * v.quadratic)
  convert h₀.add h₁ using 1 <;>
    simp [first, second] <;> ring

/-- The displayed third derivative is genuinely zero. -/
theorem hasDerivAt_second (v : ProjectiveVectorField) (s : ℂ) :
    HasDerivAt v.second (v.third s) s := by
  simpa [second, third] using
    hasDerivAt_const s (2 * v.quadratic)

end ProjectiveVectorField

/-- Regularized coefficient in the local coordinate at `s=0`. -/
def regularizedAtZero (c : ℂ) (s : ℂ) : ℂ :=
  doublePoleCoefficient c / (s - 1) ^ 2

/-- Regularized coefficient in the local coordinate at `s=1`. -/
def regularizedAtOne (c : ℂ) (s : ℂ) : ℂ :=
  doublePoleCoefficient c / s ^ 2

/-- Exact factorization of the quadratic pole at `s=0`. -/
theorem zero_doublePole_factorization
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    s ^ 2 * bipolarProjectiveConnection c s = regularizedAtZero c s := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold bipolarProjectiveConnection regularizedAtZero poleDenominator
  field_simp [h₀, h₁]

/-- Exact factorization of the quadratic pole at `s=1`. -/
theorem one_doublePole_factorization
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    (s - 1) ^ 2 * bipolarProjectiveConnection c s = regularizedAtOne c s := by
  have h₀ : s ≠ 0 := hs.1
  have h₁ : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  unfold bipolarProjectiveConnection regularizedAtOne poleDenominator
  field_simp [h₀, h₁]

/-- The regular factor at the first puncture evaluates to `-c/24`. -/
@[simp] theorem regularizedAtZero_zero (c : ℂ) :
    regularizedAtZero c 0 = doublePoleCoefficient c := by
  simp [regularizedAtZero]

/-- The regular factor at the second puncture evaluates to `-c/24`. -/
@[simp] theorem regularizedAtOne_one (c : ℂ) :
    regularizedAtOne c 1 = doublePoleCoefficient c := by
  simp [regularizedAtOne]

/-- Compact projective/Ward/pole packet. -/
theorem bipolar_projective_connection_packet
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (v : ProjectiveVectorField) :
    bipolarProjectiveConnection c s =
        -(c / 12) * bipolarSchwarzian s ∧
      bipolarProjectiveConnection c s =
        -(c / 24) * dlog01 s ^ 2 ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      deriv (bipolarProjectiveConnection c) s =
        bipolarProjectiveConnectionDeriv c s ∧
      (c / 12) * v.third s = 0 ∧
      regularizedAtZero c 0 = doublePoleCoefficient c ∧
      regularizedAtOne c 1 = doublePoleCoefficient c := by
  exact ⟨bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    deriv_bipolarSchwarzian_readout hs,
    deriv_bipolarProjectiveConnection c hs,
    (by simp [ProjectiveVectorField.third]),
    regularizedAtZero_zero c,
    regularizedAtOne_one c⟩

end InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
