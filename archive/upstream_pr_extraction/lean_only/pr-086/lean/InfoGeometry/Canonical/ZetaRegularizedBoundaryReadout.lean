import Mathlib.Tactic
import InfoGeometry.Analytic.ZetaRegVolume
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
Spectral zeta regularization property.

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
  /-- Zeta value at zero, used as anomaly/topological datum only under calibration. -/
  zetaAtZero : ℂ

/-- Zeta-regularized determinant, derived from the derivative at zero. -/
noncomputable def ZetaRegularizable.detZeta
    {SpecOp : Type*} (Z : ZetaRegularizable SpecOp) : ℂ :=
  Complex.exp (-Z.zetaDerivAtZero)

/-!
The logarithmic determinant is kept as the canonical Ray--Singer readout
`-ζ'(0)`.  It is intentionally not defined using `Complex.log`, since a
global identity `log (exp z) = z` is false without a branch hypothesis.
-/

noncomputable def logDetZeta
    {SpecOp : Type*}
    (Z : ZetaRegularizable SpecOp) : ℂ :=
  -Z.zetaDerivAtZero

/-- The logarithmic zeta determinant is the exponent appearing in the
Ray--Singer determinant.  This is an algebraic identity for the supplied
zeta datum; it does not assert a branch-dependent identity involving
`Complex.log`. -/
theorem ZetaRegularizable.detZeta_eq_exp_logDetZeta
    {SpecOp : Type*} (Z : ZetaRegularizable SpecOp) :
    Z.detZeta = Complex.exp (logDetZeta Z) := by
  rfl

/--
Construct the boundary zeta datum from an explicitly supplied analytic
continuation of a spectral zeta series.

The continuation hypothesis is the analytic input; this constructor does not
claim analytic continuation for an arbitrary operator or spectrum.
-/
noncomputable def zetaRegularizableOfContinuation
    {SpecOp : Type*}
    (eigenvalue : ℕ → ℂ)
    (domain : Set ℂ)
    (continuation : ℂ → ℂ)
    (hcontinuation :
      InfoGeometry.Analytic.IsSpectralZetaContinuation
        eigenvalue domain continuation)
    (zetaAtZero : ℂ) :
    ZetaRegularizable SpecOp where
  zeta := continuation
  zetaDerivAtZero :=
    InfoGeometry.Analytic.spectralZetaDerivativeAtZero continuation
  zeta_hasDerivAt_zero :=
    InfoGeometry.Analytic.spectralZeta_hasDerivAt_zero hcontinuation.1
  zetaAtZero := zetaAtZero

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
invariant.  This is an extra property, not an automatic theorem.
-/
def zetaTopologicalIndex
    {SpecOp : Type*} (Z : ZetaRegularizable SpecOp) : ℂ :=
  Z.zetaAtZero

/-- Weyl/KMS weighted orbit volume over a projective Drazin--Krein null boundary. -/
structure BoundaryOrbitVolume
    (Ray : Type*) where
  /-- Orbit carrier for the projective null boundary. -/
  Orbit : Type*
  /-- Weight assigned to each orbit. -/
  orbitWeight : Orbit → ℂ
  /-- The orbit-weight series is summable. -/
  summable_orbitWeight : Summable orbitWeight

noncomputable def BoundaryOrbitVolume.volume
    {Ray : Type*} (B : BoundaryOrbitVolume Ray) : ℂ :=
  ∑' x, B.orbitWeight x

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
  /-- Weyl/KMS weighted orbit volume over boundary rays. -/
  boundaryVolume : BoundaryOrbitVolume boundary.Ray

end InfoGeometry.Canonical.ZetaRegularizedBoundaryReadout
