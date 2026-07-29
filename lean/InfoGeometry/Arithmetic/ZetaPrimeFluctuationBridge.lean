import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
import InfoGeometry.Arithmetic.PrimeDistributionLaw

/-!
# InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge

Bridge from centered zeta-coordinate symmetries to prime-fluctuation law
packets.

The proved content is algebraic:

* `u = σ - 1/2` is the scale-normal coordinate;
* the critical mirror normal projector is `(u, 0)`;
* if a zero is on the critical line, its normal projector vanishes;
* a critical wave has no scale-normal envelope.

This file does not prove the Riemann explicit formula, RH, or any topological
anomaly mechanism.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
open InfoGeometry.Arithmetic.PrimeDistributionLaw

/-! ## Centered zero states and normal leakage -/

/-- A zero of a concrete complex function, expressed in the centered zeta chart. -/
structure CenteredZeroReadout where
  /-- Centered coordinate of the zero, `u = σ - 1/2`, `v = γ`. -/
  coord : ZetaCenteredChart
  /-- The concrete function whose zero is being read out. -/
  zeroFunction : ℂ → ℂ
  /-- Native pointwise zero law at the affine point represented by `coord`. -/
  isZero : ZeroAt zeroFunction (fromCentered coord).toComplex

namespace CenteredZeroReadout

/-- Scale-normal coordinate of a centered zero readout. -/
def normalCoordinate (z : CenteredZeroReadout) : ℝ :=
  z.coord.u

/-- Tangent/height coordinate of a centered zero readout. -/
def tangentCoordinate (z : CenteredZeroReadout) : ℝ :=
  z.coord.v

/-- The critical-line condition in centered coordinates. -/
def OnCriticalLine (z : CenteredZeroReadout) : Prop :=
  z.normalCoordinate = 0

/-- The critical mirror's normal projector applied to the zero readout. -/
def normalProjection (z : CenteredZeroReadout) : ZetaCenteredChart :=
  criticalNormalProjector z.coord

/-- The critical mirror's tangent projector applied to the zero readout. -/
def tangentProjection (z : CenteredZeroReadout) : ZetaCenteredChart :=
  criticalTangentProjector z.coord

/-- Normal projection has first coordinate equal to the scale-normal coordinate. -/
theorem normalProjection_u (z : CenteredZeroReadout) :
    z.normalProjection.u = z.normalCoordinate := rfl

/-- Normal projection has zero tangent coordinate. -/
theorem normalProjection_v (z : CenteredZeroReadout) :
    z.normalProjection.v = 0 := rfl

/-- Tangent projection has zero normal coordinate. -/
theorem tangentProjection_u (z : CenteredZeroReadout) :
    z.tangentProjection.u = 0 := rfl

/-- Tangent projection preserves the height coordinate. -/
theorem tangentProjection_v (z : CenteredZeroReadout) :
    z.tangentProjection.v = z.tangentCoordinate := rfl

/-- Critical-line zeros have zero normal projection. -/
theorem normalProjection_eq_zero_of_critical
    (z : CenteredZeroReadout) (hz : z.OnCriticalLine) :
    z.normalProjection = zero := by
  apply ZetaCenteredChart.ext
  · simpa [normalProjection, normalCoordinate, OnCriticalLine,
      criticalNormalProjector, zero] using hz
  · simp [normalProjection, criticalNormalProjector, zero]

/-- Vanishing normal projection is equivalent to being on the centered critical line. -/
theorem normalProjection_eq_zero_iff_critical (z : CenteredZeroReadout) :
    z.normalProjection = zero ↔ z.OnCriticalLine := by
  constructor
  · intro h
    have hu := congrArg ZetaCenteredChart.u h
    simpa [normalProjection, normalCoordinate, OnCriticalLine, criticalNormalProjector, zero] using hu
  · exact normalProjection_eq_zero_of_critical z

/-- Critical-line readouts are entirely tangent. -/
theorem tangentProjection_eq_coord_of_critical
    (z : CenteredZeroReadout) (hz : z.OnCriticalLine) :
    z.tangentProjection = z.coord := by
  apply ZetaCenteredChart.ext
  · simpa [tangentProjection, normalCoordinate, OnCriticalLine,
      criticalTangentProjector] using hz.symm
  · simp [tangentProjection, criticalTangentProjector]

end CenteredZeroReadout

/-! ## Prime-fluctuation envelope -/

/--
Algebraic envelope readout of a single explicit-formula wave.

For a zero with centered coordinate `(u, v)`, the formal wave
`x^(1/2 + u + i v)` decomposes into:

* baseline square-root envelope `x^(1/2)`;
* scale-normal envelope `x^u`;
* oscillatory phase `exp(i v log x)`.

The fields keep the readouts abstract so this module does not depend on a
specific complex-power normalization.
-/
structure PrimeWaveEnvelope where
  zero : CenteredZeroReadout
  baselineEnvelope : ℕ → ℝ
  normalEnvelope : ℕ → ℝ
  oscillatoryPhase : ℕ → ℂ
  fullWave : ℕ → ℂ
  fullWave_decomposes :
    ∀ N : ℕ,
      fullWave N =
        ((baselineEnvelope N * normalEnvelope N : ℝ) : ℂ) *
          oscillatoryPhase N
  critical_normalEnvelope_one :
    zero.OnCriticalLine → ∀ N : ℕ, normalEnvelope N = 1

namespace PrimeWaveEnvelope

/-- On the critical line, the normal envelope is identically `1`. -/
theorem normalEnvelope_eq_one_of_critical
    (W : PrimeWaveEnvelope) (hcrit : W.zero.OnCriticalLine) (N : ℕ) :
    W.normalEnvelope N = 1 :=
  W.critical_normalEnvelope_one hcrit N

/-- On the critical line, the full wave has no scale-normal envelope. -/
theorem fullWave_eq_baseline_mul_phase_of_critical
    (W : PrimeWaveEnvelope) (hcrit : W.zero.OnCriticalLine) (N : ℕ) :
    W.fullWave N = ((W.baselineEnvelope N : ℝ) : ℂ) * W.oscillatoryPhase N := by
  rw [W.fullWave_decomposes N, W.normalEnvelope_eq_one_of_critical hcrit N]
  simp

end PrimeWaveEnvelope

end InfoGeometry.Arithmetic.ZetaPrimeFluctuationBridge
