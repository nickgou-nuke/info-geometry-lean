import Mathlib.Data.Complex.Basic

/-!
# InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

Data socket for the relative-determinant/scattering lane.

This file is intentionally structural. It does not prove analytic continuation,
pole/zero conversion, RH, or a self-adjoint MBK determinant identity.  Those
unsupported claims are exposed as explicit `sorry` debt, not hidden as arbitrary
packet propositions.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeDeterminantScatteringSocket

universe uH uScat

/--
Packet for relative determinant and scattering readouts.

It contains carriers, readouts, and predicates only.  It carries no theorem
fields.
-/
structure RelativeDeterminantScatteringPacket where
  /-- Underlying spectral carrier (Hilbert/operator side). -/
  SpectralCarrier : Type uH

  /-- Carrier for scattering data (matrix/operator-valued side). -/
  ScatteringCarrier : Type uScat

  /-- Relative determinant readout (zeta-regularized or relative Fredholm lane). -/
  relativeDeterminant : ℂ → ℂ

  /-- Scattering readout channel (symbolic socket; concrete model is external). -/
  scatteringMatrix : ℂ → ScatteringCarrier

  /-- Predicate that `s` is a determinant-side pole (owner-specified notion). -/
  IsDeterminantPole : ℂ → Prop

  /-- Predicate that `s` is a determinant-side zero (owner-specified notion). -/
  IsDeterminantZero : ℂ → Prop

  /-- Predicate that `s` is a scattering-side resonance/pole (owner-specified notion). -/
  IsScatteringResonance : ℂ → Prop

namespace RelativeDeterminantScatteringPacket

end RelativeDeterminantScatteringPacket

/-- Owner target for the relative-determinant/scattering witness lane. -/
abbrev RelativeDeterminantScatteringTarget : Type (max (uH + 1) (uScat + 1)) :=
  RelativeDeterminantScatteringPacket.{uH, uScat}

/-- Constructor for the relative-determinant/scattering owner target. -/
def constructRelativeDeterminantScatteringTarget
    (P : RelativeDeterminantScatteringPacket.{uH, uScat}) :
    RelativeDeterminantScatteringTarget := P

end InfoGeometry.Canonical.RelativeDeterminantScatteringSocket
