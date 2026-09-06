/-
InfoGeometry/OperatorAlgebra/PO55RicciFlux.lean

Ricci-flux and grade-slippage data for the PO(5,5)/TKK ledger.

This file records the precise algebraic place where an "Einstein anomaly" can
live in the closed conformal stack:

  [g₋₁, g₊₁] should land in g₀.

For a perfect PO(5,5)/TKK model, the cross bracket of translations and special
conformal generators closes exactly into the grade-zero pivot.  In an observed,
lossy, projected, or renormalized representation, there may be a defect between

  observedBracket (ρ Pₐ) (ρ K_b)

and

  ρ (expected grade-zero element).

That defect is the algebraic "Ricci-flux" readout.  It is not asserted to be the
Einstein tensor by definition; concrete metric/connection modules must supply
the contraction/readout theorem.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.TKKClosure
import InfoGeometry.OperatorAlgebra.PO55ConformalClosure

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## Exact TKK cross defect -/

namespace TKKLieClosure

variable
    {J L : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : TKKLieClosure J L)

/--
The exact TKK cross-grade defect.

This is the unobserved algebraic defect

`[g₋₁(x), g₊₁(y)] - g₀(x,y)`.

For a supplied `TKKLieClosure`, this vanishes by the TKK cross-closure field.
-/
def exactCrossDefect
    (x y : J) : L :=
  T.lie.bracket (T.neg x) (T.pos y) - T.zero x y

/-- Exact TKK closure has no cross-grade defect. -/
theorem exactCrossDefect_eq_zero
    (x y : J) :
    T.exactCrossDefect x y = 0 := by
  dsimp [exactCrossDefect]
  rw [T.bracket_neg_pos]
  simp

end TKKLieClosure

/-! ## 3. Observed/projected TKK bracket and grade slippage -/

/--
An observed representation of a TKK Lie closure.

This is the correct place to model lossy optics, projected states, regularized
readouts, nonunitary channels, or coarse-grained gravitational observables: the
observed bracket need not agree definitionally with the represented TKK bracket.
-/
structure ObservedTKKBracket
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (T : TKKLieClosure J L) where
  /-- Representation/projection into the observed readout carrier. -/
  repr : L →ₗ[ℝ] Obs

  /-- Bracket or commutator seen by the observed/coarse-grained model. -/
  observedBracket : Obs → Obs → Obs

  /-- Left additivity of the observed bracket. -/
  observedBracket_add_left :
    ∀ x y z : Obs,
      observedBracket (x + y) z =
        observedBracket x z + observedBracket y z

  /-- Left scalar compatibility of the observed bracket. -/
  observedBracket_smul_left :
    ∀ (c : ℝ) (x y : Obs),
      observedBracket (c • x) y =
        c • observedBracket x y

namespace ObservedTKKBracket

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {T : TKKLieClosure J L}
    (R : ObservedTKKBracket J L Obs T)

/--
Observed cross-grade slippage:

`[ρ(g₋₁ x), ρ(g₊₁ y)]_obs - ρ(g₀(x,y))`.

This is the algebraic readout for an Einstein/Ricci-flux-type anomaly.
-/
def crossGradeSlippage
    (x y : J) : Obs :=
  R.observedBracket (R.repr (T.neg x)) (R.repr (T.pos y)) -
    R.repr (T.zero x y)

/-- Exact observed closure implies zero grade slippage. -/
theorem crossGradeSlippage_eq_zero_of_exact
    {x y : J}
    (h : R.observedBracket (R.repr (T.neg x)) (R.repr (T.pos y)) =
      R.repr (T.zero x y)) :
    R.crossGradeSlippage x y = 0 := by
  dsimp [crossGradeSlippage]
  rw [h]
  simp

end ObservedTKKBracket

/-! ## 4. Ricci-flux readout -/

/--
A scalar readout of observed TKK grade slippage.

The name `RicciFlux` is intentionally a readout, not a definition of the
Ricci tensor.  A metric/connection module must later prove that this scalar or
tensorial readout equals a curvature contraction.
-/
structure RicciFluxReadout
    (J L Obs : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    (T : TKKLieClosure J L) where
  observed : ObservedTKKBracket J L Obs T

  /-- Scalar or component readout of a slippage element. -/
  readout : J → J → Obs → ℝ

  readout_zero :
    ∀ x y : J, readout x y 0 = 0

namespace RicciFluxReadout

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    {T : TKKLieClosure J L}
    (R : RicciFluxReadout J L Obs T)

/-- Scalar Ricci-flux component associated to a pair of TKK coordinates. -/
def flux
    (x y : J) : ℝ :=
  R.readout x y (R.observed.crossGradeSlippage x y)

/-- Exact observed TKK closure gives zero scalar flux. -/
theorem flux_eq_zero_of_exact
    {x y : J}
    (h : R.observed.observedBracket
          (R.observed.repr (T.neg x))
          (R.observed.repr (T.pos y)) =
        R.observed.repr (T.zero x y)) :
    R.flux x y = 0 := by
  dsimp [flux]
  rw [R.observed.crossGradeSlippage_eq_zero_of_exact h]
  exact R.readout_zero x y

/-- Zero observed grade slippage gives zero scalar flux. -/
theorem flux_eq_zero_of_observed_eq
    {x y : J}
    (h : R.observed.crossGradeSlippage x y = 0) :
    R.flux x y = 0 := by
  dsimp [flux]
  rw [h]
  exact R.readout_zero x y

end RicciFluxReadout

/-! ## 5. Hidden-sector inertia as a property, not an identification -/

/--
A dark/hidden-sector inertia readout for the positive TKK grade.

This deliberately does not identify dark matter with the commutant or with the
`g₊₁` grade.  It records the hypotheses a concrete model must satisfy for the
positive-grade/commutant-side momentum to be gravitationally visible but hidden
from a chosen visible probe.
-/
structure HiddenInertiaReadout
    (J L Probe : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : TKKLieClosure J L) where
  /-- Probe/observable readout, e.g. electromagnetic, optical, or matter-sector. -/
  probe : L → Probe

  /-- Inertial/gravitational readout of the positive grade. -/
  inertia : J → ℝ

  /-- Positive grade is invisible to the chosen probe. -/
  positive_grade_probe_dark :
    ∀ x : J, probe (T.pos x) = probe 0

  /-- Positive grade contributes nontrivially to the inertial/gravitational ledger. -/
  positive_grade_inertial :
    ∃ x : J, inertia x ≠ 0


/-! ## 6. Conformal height -/

/--
A positive conformal height on the projective null quadric.

This is the correct place to attach the Bilingual Poincaré height.  It is not
provided by `PO(5,5)` alone; it requires a chart, positivity domain, and
projective normalization/readout.
-/
structure ConformalHeightDatum
    (W : Type*) [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  stateDomain : Set (ConformalState55 Q)
  height : ConformalState55 Q → ℝ

  /-- Logarithmic height coordinate on the chart. -/
  logHeight : ConformalState55 Q → ℝ

  /-- Height is the exponential of the chosen logarithmic height coordinate. -/
  height_eq_exp_logHeight :
    ∀ X : ConformalState55 Q, X ∈ stateDomain → height X = Real.exp (logHeight X)

namespace ConformalHeightDatum

variable
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {Q : SplitQuadratic55 W}
    (H : ConformalHeightDatum W Q)

/-- The conformal height is positive on the declared chart domain. -/
theorem height_pos
    (X : ConformalState55 Q)
    (hX : X ∈ H.stateDomain) :
    0 < H.height X := by
  rw [H.height_eq_exp_logHeight X hX]
  exact Real.exp_pos _

end ConformalHeightDatum

/--
A Bilingual Poincaré metric datum over a conformal-height chart.

Concrete modules can instantiate this by a Fisher/Kähler/Poincaré formula, for
example `ds² = (dx² + dy²)/y²` on an upper-half-plane chart.
-/
structure BilingualPoincareMetricDatum
    (W : Type*) [AddCommGroup W] [Module ℝ W]
  (Q : SplitQuadratic55 W) where
  height : ConformalHeightDatum W Q
  metricReadout : ConformalState55 Q → ConformalState55 Q → ℝ

  /-- Symmetry of the metric readout. -/
  metric_symm :
    ∀ X Y : ConformalState55 Q, metricReadout X Y = metricReadout Y X

  /-- Nonnegativity of the diagonal readout on the chart domain. -/
  metric_self_nonneg :
    ∀ X : ConformalState55 Q, X ∈ height.stateDomain → 0 ≤ metricReadout X X

end InfoGeometry.OperatorAlgebra
