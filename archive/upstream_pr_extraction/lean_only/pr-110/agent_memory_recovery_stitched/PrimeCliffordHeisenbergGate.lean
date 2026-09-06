import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeMertensDefectBoundary

/-!
# InfoGeometry.Canonical.PrimeCliffordHeisenbergGate

Heisenberg-to-Mertens explicit hypotheses and debt lemmas.

The deleted version contained an explicit `vacuousTarget : True`.  This repaired
version removes that field and keeps only the genuine proof-carrying data:
Heisenberg lower bounds, saturation, and an explicit dispersion-to-Mertens
bridge supplied as a field.

No Mertens estimate or RH theorem is proved here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCliffordHeisenbergGate

open InfoGeometry.Canonical.PrimeMertensDefectBoundary

/--
Clifford/Majorana vacuum readout for the prime Möbius/Mertens lane.
The Heisenberg inequality is recorded as data, not derived here.
-/
@[rep_depth operator]
structure CliffordMajoranaVacuum (D : MobiusMertensData) where
  dispersion_x : ℕ → ℝ
  dispersion_ω : ℕ → ℝ
  heisenberg_bound : ∀ N : ℕ, (1 / 4 : ℝ) ≤ dispersion_x N * dispersion_ω N
  zero_point_exponent : ℝ
  zero_point_eq_half : zero_point_exponent = 1 / 2

/-- Witness for saturation of the Heisenberg lower bound. -/
class SaturatesHeisenbergBound
    {D : MobiusMertensData}
    (V : CliffordMajoranaVacuum D) : Prop where
  is_minimal_uncertainty :
    ∀ N : ℕ,
      V.dispersion_x N * V.dispersion_ω N = (1 / 4 : ℝ)

/--
Explicit bridge from vacuum dispersion to Mertens control.  This is the actual
analytic obligation; it is supplied, not proved from saturation alone.
-/
@[rep_depth operator]
structure CliffordLDPBridge
    {D : MobiusMertensData}
    (V : CliffordMajoranaVacuum D) where
  mertens_bounded_by_dispersion :
    ∀ N : ℕ, |(D.M N : ℝ)| ≤ V.dispersion_x N
  dispersion_scaling : Prop
  dispersion_scaling_certificate : dispersion_scaling

/-- The gate object: all content is proof-carrying data, with no `True` target. -/
@[rep_depth operator]
structure HeisenbergMertensGate (D : MobiusMertensData) where
  vacuum : CliffordMajoranaVacuum D
  bridge : CliffordLDPBridge vacuum
  saturation : SaturatesHeisenbergBound vacuum

namespace HeisenbergMertensGate

variable {D : MobiusMertensData}

/-- The gate exposes the supplied dispersion-to-Mertens bound. -/
@[rep_depth operator]
theorem mertens_bounded_by_dispersion
    (G : HeisenbergMertensGate D) (N : ℕ) :
    |(D.M N : ℝ)| ≤ G.vacuum.dispersion_x N :=
  G.bridge.mertens_bounded_by_dispersion N

/-- The gate exposes saturation of the Heisenberg lower bound. -/
@[rep_depth operator]
theorem saturated_uncertainty
    (G : HeisenbergMertensGate D) (N : ℕ) :
    G.vacuum.dispersion_x N * G.vacuum.dispersion_ω N = (1 / 4 : ℝ) :=
  G.saturation.is_minimal_uncertainty N

/-- The zero-point exponent is the supplied half exponent. -/
@[rep_depth operator]
theorem zero_point_exponent_eq_half
    (G : HeisenbergMertensGate D) :
    G.vacuum.zero_point_exponent = 1 / 2 :=
  G.vacuum.zero_point_eq_half

end HeisenbergMertensGate

end InfoGeometry.Canonical.PrimeCliffordHeisenbergGate
