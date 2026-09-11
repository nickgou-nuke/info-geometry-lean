import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KreinDrazinBoundarySupport

/-!
# Zeta-Regularized Boundary Readout

Zeta regularization is not a trace on a Type III factor.  It is a
spectral-triple/compressed-operator readout attached to a chosen regular-sector
model after a Drazin split.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaRegularizedBoundaryReadout

open InfoGeometry.Canonical.KreinDrazinBoundarySupport

/--
Spectral zeta regularization witness.

`SpecOp` is the positive/sectorial regular spectral operator supplied by a
chosen spectral model, typically a regular-sector compression.
-/
structure ZetaRegularizable
    (_SpecOp : Type*) where
  /-- Spectral zeta function or its meromorphic continuation. -/
  zeta : ℂ → ℂ
  /-- Derivative of the zeta function at zero. -/
  zetaDerivAtZero : ℂ
  /-- The supplied derivative is the actual derivative at zero. -/
  zeta_hasDerivAt_zero : HasDerivAt zeta zetaDerivAtZero 0
  /-- Zeta-regularized determinant. -/
  detZeta : ℂ
  /-- Ray--Singer style determinant definition. -/
  detZeta_def : detZeta = Complex.exp (-zetaDerivAtZero)
  /-- Zeta value at zero, used as anomaly/topological datum only under calibration. -/
  zetaAtZero : ℂ

/-- The zeta determinant is the exponential of minus the derivative at zero. -/
theorem det_zeta_eq_exp_neg_zeta_derivative
    {SpecOp : Type*}
    (Z : ZetaRegularizable SpecOp) :
    Z.detZeta = Complex.exp (-Z.zetaDerivAtZero) :=
  Z.detZeta_def

/- The derivative witness is exposed directly instead of through a semantic
label for analytic continuation. -/
theorem zeta_has_derivative_at_zero
    {SpecOp : Type*}
    (Z : ZetaRegularizable SpecOp) :
    HasDerivAt Z.zeta Z.zetaDerivAtZero 0 :=
  Z.zeta_hasDerivAt_zero

/--
A Drazin-regular spectral readout.

This records that the zeta operator is the regular-sector spectral model, not
a determinant or trace on the ambient Type III algebra.
-/
structure DrazinRegularZetaReadout
    (K Op SpecOp : Type*)
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Regular-sector spectral operator/model. -/
  spectralOperator : SpecOp
  /-- Zeta data attached to the regular-sector model. -/
  zetaData : ZetaRegularizable SpecOp

/--
Calibration connecting `ζ(0)` or the zeta determinant to a topological boundary
invariant.  This is an extra witness, not an automatic theorem.
-/
structure ZetaTopologicalCalibration
    (SpecOp : Type*)
    (Z : ZetaRegularizable SpecOp) where
  /-- Topological/anomaly index readout. -/
  topologicalIndex : ℂ
  /-- Calibration equating the index with `ζ(0)`. -/
  index_eq_zetaAtZero : topologicalIndex = Z.zetaAtZero

/-- Under a calibration witness, the topological index equals `ζ(0)`. -/
theorem calibrated_topological_index_eq_zeta_zero
    {SpecOp : Type*}
    (Z : ZetaRegularizable SpecOp)
    (C : ZetaTopologicalCalibration SpecOp Z) :
    C.topologicalIndex = Z.zetaAtZero :=
  C.index_eq_zetaAtZero

/-- Weyl/KMS weighted orbit volume over a projective Drazin--Krein null boundary. -/
structure BoundaryOrbitVolume
    (Ray : Type*) where
  /-- Orbit carrier for the projective null boundary. -/
  Orbit : Type*
  /-- Weight assigned to each orbit. -/
  orbitWeight : Orbit → ℂ
  /-- Total boundary volume/readout. -/
  volume : ℂ
  /-- The volume is the actual orbit-weight sum. -/
  volume_eq_sum : volume = ∑' x, orbitWeight x
  /-- The orbit-weight series is summable. -/
  summable_orbitWeight : Summable orbitWeight

/--
Zeta-regularized Drazin--Krein boundary geometry package.

Regular determinant:
`detζ(Δ_reg) = exp(-ζ'(0))`.

Boundary:
`P(Ran(H_L) ∩ Null_J)`.

Topological volume:
Weyl/KMS weighted orbit count over the boundary.
-/
structure ZetaBoundaryGeometryReadout
    (K Op SpecOp : Type*)
    [Ring Op]
    [SMul ℝ K] where
  /-- Krein--Drazin boundary support. -/
  support : KreinDrazinBoundarySupport K Op
  /-- Projectivized null boundary. -/
  boundary : ProjectiveDrazinNullBoundary K Op support
  /-- Regular-sector zeta readout. -/
  zetaReadout : DrazinRegularZetaReadout K Op SpecOp support
  /-- Calibration from zeta data to topology/anomaly data. -/
  topologicalCalibration :
    ZetaTopologicalCalibration SpecOp zetaReadout.zetaData
  /-- Weyl/KMS weighted orbit volume over boundary rays. -/
  boundaryVolume : BoundaryOrbitVolume boundary.Ray

/-- The zeta readout in a geometry packet has the expected determinant formula. -/
theorem packet_det_zeta_eq_exp_neg_zeta_derivative
    {K Op SpecOp : Type*}
    [Ring Op]
    [SMul ℝ K]
    (G : ZetaBoundaryGeometryReadout K Op SpecOp) :
    G.zetaReadout.zetaData.detZeta =
      Complex.exp (-G.zetaReadout.zetaData.zetaDerivAtZero) :=
  det_zeta_eq_exp_neg_zeta_derivative G.zetaReadout.zetaData

/-- The calibrated topological index in a geometry packet equals `ζ(0)`. -/
theorem packet_topological_index_eq_zeta_zero
    {K Op SpecOp : Type*}
    [Ring Op]
    [SMul ℝ K]
    (G : ZetaBoundaryGeometryReadout K Op SpecOp) :
    G.topologicalCalibration.topologicalIndex =
      G.zetaReadout.zetaData.zetaAtZero :=
  calibrated_topological_index_eq_zeta_zero
    G.zetaReadout.zetaData
    G.topologicalCalibration

end InfoGeometry.Canonical.ZetaRegularizedBoundaryReadout
