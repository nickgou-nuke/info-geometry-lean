/-
InfoGeometry/OperatorAlgebra/PO55RicciFlux.lean

Ricci-flux and grade-slippage sockets for the PO(5,5)/TKK ledger.

This file records the precise algebraic place where an "Einstein anomaly" can
live in the closed conformal stack:

  [g₋₁, g₊₁] should land in g₀.

For a perfect PO(5,5)/TKK model, the cross bracket of translations and special
conformal generators closes exactly into the grade-zero pivot.  In an observed,
lossy, projected, or renormalized representation, there may be a defect between

  observedBracket (ρ Pₐ) (ρ K_b)

and

  ρ (expected grade-zero element).

That defect is the algebraic "Ricci-flux" socket.  It is not asserted to be the
Einstein tensor by definition; concrete metric/connection modules must supply
the contraction/readout theorem.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TKKClosure
import InfoGeometry.OperatorAlgebra.PO55ConformalClosure
import InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization
import InfoGeometry.Meta.SocketTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Abstract conformal bracket socket -/

/--
A conformal-bracket socket for a signature `(4,4)` conformal algebra.

The intended relation is the standard conformal algebra pattern

`[P_a, K_b] = 2 • (η_ab • D + M_ab)`,

up to the sign convention chosen by the concrete model.  This structure carries
that convention explicitly in `cross_closure`.
-/
@[socket_debt_tag]
structure ConformalBracketSocket
    (Idx L : Type*) [AddCommGroup L] [Module ℝ L] where
  /-- Bracket in the conformal Lie socket. -/
  bracket : L → L → L

  /-- Split metric coefficients on the index set. -/
  eta : Idx → Idx → ℝ

  /-- Translation generators, grade `-1`. -/
  P : Idx → L

  /-- Special conformal generators, grade `+1`. -/
  K : Idx → L

  /-- Lorentz/split-orthogonal grade-zero generators. -/
  M : Idx → Idx → L

  /-- Dilation/Weyl/modular grade-zero generator. -/
  D : L

  /-- Exact cross-bracket closure in the chosen convention. -/
  cross_closure :
    ∀ a b : Idx,
      bracket (P a) (K b) =
        2 • ((eta a b) • D + M a b)

  /-- Translation grade is abelian. -/
  translations_abelian :
    ∀ a b : Idx, bracket (P a) (P b) = 0

  /-- Special conformal grade is abelian. -/
  specials_abelian :
    ∀ a b : Idx, bracket (K a) (K b) = 0

  /-- The full Jacobi/regularity certificate is left to concrete models. -/
  lie_regular : Prop

namespace ConformalBracketSocket

variable
    {Idx L : Type*} [AddCommGroup L] [Module ℝ L]
    (C : ConformalBracketSocket Idx L)

/-- The expected grade-zero cross bracket `[P_a,K_b]`. -/
def expectedCross
    (a b : Idx) : L :=
  2 • ((C.eta a b) • C.D + C.M a b)

/-- The exact cross-bracket defect.  For a closed model this is zero. -/
def crossDefect
    (a b : Idx) : L :=
  C.bracket (C.P a) (C.K b) - C.expectedCross a b

/-- In the exact conformal/TKK model, the cross defect vanishes. -/
theorem crossDefect_eq_zero
    (a b : Idx) :
    C.crossDefect a b = 0 := by
  dsimp [crossDefect, expectedCross]
  rw [C.cross_closure]
  simp

end ConformalBracketSocket

/-! ## 2. Exact TKK cross defect -/

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

  /-- Regularity/domain certificate for the observed bracket. -/
  observedBracket_regular : Prop

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

This is the algebraic socket for an Einstein/Ricci-flux-type anomaly.
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

/-! ## 4. Ricci-flux readout socket -/

/--
A scalar readout of observed TKK grade slippage.

The name `RicciFlux` is intentionally a readout socket, not a definition of the
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

  /-- Certificate that this is the intended curvature/anomaly observable. -/
  curvatureInterpretation : Prop

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

/-! ## 5. Hidden-sector inertia as a hypothesis, not an identification -/

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

  /-- Positive grade contributes to the inertial/gravitational ledger. -/
  positive_grade_inertial : Prop

  /-- Stability under admissible PO(5,5)/TKK flow. -/
  stable_under_admissible_flow : Prop


/--
Hidden conformal inertia hypothesis.

The `g₊₁` / `e₊` / commutant-side sector is treated as a dark-inertia carrier
only if it is invisible to ordinary probes but visible through gravitational or
curvature readouts.

This is intentionally a model hypothesis, not a theorem of `PO(5,5)` alone.
-/
structure HiddenConformalInertia
    (J L Probe Geometry : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Geometry] [Module ℝ Geometry] where
  /-- Negative/visible translation grade. -/
  gMinus : J →ₗ[ℝ] L

  /-- Positive/hidden special-conformal grade. -/
  gPlus : J →ₗ[ℝ] L

  /-- Grade-zero curvature/metric ledger. -/
  gZeroReadout : L → Geometry

  /-- Ordinary probe, e.g. electromagnetic or visible-sector readout. -/
  probe : L → Probe

  /-- Inertia/mass-like scalar readout. -/
  inertia : J → ℝ

  /-- Hidden sector is invisible to ordinary probes. -/
  gPlus_probe_dark :
    ∀ x : J, probe (gPlus x) = probe 0

  /-- Hidden sector carries inertial content on selected states. -/
  gPlus_inertial : Prop

  /--
  The hidden sector back-reacts through the conformal/TKK ledger.

  This is where `[g₋₁,g₊₁] → g₀` becomes visible as curvature.
  -/
  cross_bracket_gravitationally_visible : Prop

  /-- Stability under admissible modular/conformal flow. -/
  stable_under_admissible_flow : Prop

  /-- Phenomenological matching: lensing, clustering, CMB, etc. -/
  phenomenology : Prop

/--
The positive-grade sector is a dark-matter candidate in a supplied model.

This does not identify the sector with observed dark matter by definition.  It
records the exact witness obligations: probe darkness, inertial content,
gravitational visibility through the conformal ledger, stability, and
phenomenological calibration.
-/
structure IsDarkMatterCandidate
    (J L Probe Geometry : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (H : HiddenConformalInertia J L Probe Geometry) where
  probe_dark :
    ∀ x : J, H.probe (H.gPlus x) = H.probe 0

  inertial : Prop

  gravitationally_visible : Prop

  stable : Prop

  phenomenology : Prop

namespace HiddenConformalInertia

variable
    {J L Probe Geometry : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (H : HiddenConformalInertia J L Probe Geometry)

/-- Re-export: the positive grade is invisible to the chosen ordinary probe. -/
theorem probe_dark
    (x : J) :
    H.probe (H.gPlus x) = H.probe 0 :=
  H.gPlus_probe_dark x

/--
A fully witnessed hidden-conformal-inertia datum is a dark-matter candidate in
that model.
-/
def isDarkMatterCandidate :
    IsDarkMatterCandidate J L Probe Geometry H where
  probe_dark := H.gPlus_probe_dark
  inertial := H.gPlus_inertial
  gravitationally_visible := H.cross_bracket_gravitationally_visible
  stable := H.stable_under_admissible_flow
  phenomenology := H.phenomenology

end HiddenConformalInertia

/-! ## 6. Conformal height socket -/

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

  height_pos :
    ∀ X : ConformalState55 Q, X ∈ stateDomain → 0 < height X


  /-- Compatibility with the chosen Weyl/log-radial coordinate. -/
  log_height_compatibility : Prop

/--
A Bilingual Poincaré metric socket over a conformal-height chart.

Concrete modules can instantiate this by a Fisher/Kähler/Poincaré formula, for
example `ds² = (dx² + dy²)/y²` on an upper-half-plane chart.
-/
structure BilingualPoincareMetricDatum
    (W : Type*) [AddCommGroup W] [Module ℝ W]
    (Q : SplitQuadratic55 W) where
  height : ConformalHeightDatum W Q
  metricReadout : ConformalState55 Q → ConformalState55 Q → ℝ
  conformal_covariance : Prop
  nondegenerate_on_chart : Prop
  boundary_is_projective_null_quadric : Prop

end InfoGeometry.OperatorAlgebra
