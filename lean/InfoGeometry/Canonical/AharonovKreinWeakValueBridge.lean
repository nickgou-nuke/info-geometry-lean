import Mathlib.Tactic
import InfoGeometry.Canonical.QuantumSpinNavierStokes
import InfoGeometry.Canonical.AAVWeakMeasurementKleinSeamBridge
import InfoGeometry.OperatorAlgebra.KreinIsotropicCone

/-!
# Aharonov weak values at a Krein seam

This module makes the proposed weak-value mechanism explicit at the level that
the existing repository supports:

* a Krein null mode is a nonzero state with zero indefinite quadratic form;
* a cross-sheet transition amplitude is tracked separately;
* a classical readout is a quotient only when its denominator is nonzero;
* an explicit positive time-gap path gives arbitrarily large weak values and a
  reciprocal-square scalar barrier.

The null-mode condition does not, by itself, imply that the cross-sheet
transition amplitude vanishes.  Likewise, this module does not assert that a
Navier--Stokes velocity has this reconstruction, that a scalar proxy is
enstrophy, or that a quantum seam proves PDE blow-up or post-singularity
self-healing.
-/

noncomputable section

namespace InfoGeometry.Canonical.AharonovKreinWeakValueBridge

open InfoGeometry.Canonical.AAVWeakMeasurementKleinSeam
open InfoGeometry.Canonical.ZornModularAAV

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The indefinite quadratic form determined by a fundamental symmetry. -/
def kreinQuadratic
    (K : InfoGeometry.OperatorAlgebra.KreinMetricDatum H) (ψ : H) : ℝ :=
  inner (𝕜 := ℝ) ψ (K.eta ψ)

/-- A nonzero isotropic state for the repository's Krein metric datum. -/
def KreinNullMode
    (K : InfoGeometry.OperatorAlgebra.KreinMetricDatum H) (ψ : H) : Prop :=
  ψ ≠ 0 ∧ kreinQuadratic K ψ = 0

/-- Real cross-sheet transition amplitude used by the finite-dimensional bridge. -/
def transitionAmplitude (post pre : H) : ℝ :=
  inner (𝕜 := ℝ) post pre

/-- Explicit cancellation of the cross-sheet transition amplitude. -/
def CrossSheetTransitionZero (post pre : H) : Prop :=
  transitionAmplitude post pre = 0

/-- A seam datum keeps Krein nullity and cross-sheet cancellation independent. -/
structure KreinAAVSeamDatum where
  metric : InfoGeometry.OperatorAlgebra.KreinMetricDatum H
  nullState : H
  postState : H
  preState : H
  nullMode : KreinNullMode metric nullState
  crossSheetZero : CrossSheetTransitionZero postState preState

/-- A scalar classical readout whose weak-value denominator is in its domain. -/
structure ClassicalVelocityWeakReadout where
  velocity : ℝ
  numerator : ℝ
  denominator : ℝ
  denominator_ne_zero : denominator ≠ 0
  velocity_eq_weak_value :
    velocity = aharonovWeakValue numerator denominator

namespace ClassicalVelocityWeakReadout

variable (R : ClassicalVelocityWeakReadout)

/-- Clearing the weak-value denominator recovers the numerator. -/
theorem denominator_mul_velocity :
    R.denominator * R.velocity = R.numerator := by
  rw [R.velocity_eq_weak_value]
  exact weak_value_amplification_scaling
    R.numerator R.denominator R.denominator rfl R.denominator_ne_zero

/-- A scalar reciprocal-square proxy for the cost of a singular readout. -/
def reciprocalSquareBarrier (den : ℝ) : ℝ :=
  1 / (den * den)

/-- A scalar gradient proxy; it is not a spatial enstrophy functional. -/
def scalarGradientBarrier (velocity : ℝ) : ℝ :=
  velocity ^ 2

/-- The weak-value square is exactly a numerator square times the proxy barrier. -/
theorem velocity_sq_eq_numerator_sq_mul_barrier :
    scalarGradientBarrier R.velocity =
      R.numerator ^ 2 * reciprocalSquareBarrier R.denominator := by
  rw [R.velocity_eq_weak_value]
  dsimp [scalarGradientBarrier, reciprocalSquareBarrier, aharonovWeakValue]
  field_simp [R.denominator_ne_zero] <;> ring

end ClassicalVelocityWeakReadout

/-- A positive denominator path approaching zero from below at time T. -/
def DenominatorApproachesZeroFromBelow (den : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ t : ℝ, t < T ∧ 0 < den t ∧ den t < ε

/-- An observable is arbitrarily large before a finite reference time. -/
def ArbitrarilyLargeBefore (f : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ t : ℝ, t < T ∧ f t > M

/-- The weak-value path with constant numerator and shrinking positive gap. -/
def weakValueAlongTime (a T t : ℝ) : ℝ :=
  aharonovWeakValue a (T - t)

/-- The canonical time gap has the required one-sided approach property. -/
theorem timeGap_approaches_zero_from_below (T : ℝ) :
    DenominatorApproachesZeroFromBelow (fun t : ℝ => T - t) T := by
  intro ε hε
  refine ⟨T - ε / 2, by linarith, by linarith, by linarith⟩

/-- A sufficiently small positive time gap makes the weak value exceed any bound. -/
theorem weakValueAlongTime_exceeds
    (a T M ε : ℝ) (ha : 0 < a) (hM : 0 < M)
    (hε : 0 < ε) (hε_bound : ε < a / M) :
    ∃ t : ℝ, t < T ∧ weakValueAlongTime a T t > M := by
  refine ⟨T - ε, by linarith, ?_⟩
  dsimp [weakValueAlongTime, aharonovWeakValue]
  have hgap : T - (T - ε) = ε := by ring
  rw [hgap]
  exact weak_amplification_bound a ε M hε hM hε_bound

/-- The explicit positive-numerator path is unbounded before T. -/
theorem weakValueAlongTime_arbitrarilyLarge
    (a T : ℝ) (ha : 0 < a) :
    ArbitrarilyLargeBefore (weakValueAlongTime a T) T := by
  intro M hM
  let ε : ℝ := a / (2 * M)
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos ha (by positivity)
  have hε_bound : ε < a / M := by
    dsimp [ε]
    apply (lt_div_iff₀ hM).2
    have hcalc : a / (2 * M) * M = a / 2 := by
      field_simp [ne_of_gt hM] <;> ring
    rw [hcalc]
    nlinarith
  exact weakValueAlongTime_exceeds a T M ε ha hM hε hε_bound

/-- The reciprocal-square proxy evaluated along the same shrinking gap. -/
def reciprocalSquareBarrierAlongTime (T t : ℝ) : ℝ :=
  ClassicalVelocityWeakReadout.reciprocalSquareBarrier (T - t)

/-- The scalar reciprocal-square barrier is arbitrarily large before T. -/
theorem reciprocalSquareBarrierAlongTime_arbitrarilyLarge (T : ℝ) :
    ArbitrarilyLargeBefore (reciprocalSquareBarrierAlongTime T) T := by
  intro M hM
  let ε : ℝ := 1 / (M + 1)
  have hM1 : 0 < M + 1 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos zero_lt_one hM1
  refine ⟨T - ε, by linarith, ?_⟩
  dsimp [reciprocalSquareBarrierAlongTime,
    ClassicalVelocityWeakReadout.reciprocalSquareBarrier]
  have hgap : T - (T - ε) = ε := by ring
  rw [hgap]
  have hbar : 1 / (ε * ε) = (M + 1) * (M + 1) := by
    dsimp [ε]
    field_simp [ne_of_gt hM1] <;> ring
  rw [hbar]
  nlinarith

end InfoGeometry.Canonical.AharonovKreinWeakValueBridge
