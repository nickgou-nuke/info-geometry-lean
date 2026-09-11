import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

/--
The affine channel invariant produced by a null BCFW deformation:

  P(z)² = P² + z * slope.

In physical applications, `slope = 2 ⟪P, q⟫`.
-/
def bcfwChannelInvariant
    (P_sq slope z : ℂ) : ℂ :=
  P_sq + z * slope

/-- A finite BCFW channel pole is a zero of the shifted channel invariant. -/
def IsBCFWChannelPole
    (P_sq slope z : ℂ) : Prop :=
  bcfwChannelInvariant P_sq slope z = 0

/-- The affine shifted channel goes on shell at `-P_sq / slope`. -/
theorem bcfw_channel_pole_value
    (P_sq slope : ℂ)
    (hslope : slope ≠ 0) :
    IsBCFWChannelPole
      P_sq slope (-P_sq / slope) := by
  unfold IsBCFWChannelPole bcfwChannelInvariant
  rw [div_mul_cancel₀ (-P_sq) hslope]
  ring

/-- A finite affine channel has no other pole when its slope is nonzero. -/
theorem bcfw_channel_pole_unique
    (P_sq slope z : ℂ) (hslope : slope ≠ 0)
    (hz : IsBCFWChannelPole P_sq slope z) :
    z = -P_sq / slope := by
  have hz0 : P_sq + z * slope = 0 := by
    simpa [IsBCFWChannelPole, bcfwChannelInvariant] using hz
  have hz' : z * slope = -P_sq := by
    exact add_eq_zero_iff_eq_neg.mp (by simpa [add_comm] using hz0)
  exact (eq_div_iff hslope).2 hz'

/--
The factorized numerator of one BCFW channel.

This is only the algebraic numerator; it is not yet a theorem about residues,
canonical forms, helicity sums, or the amplituhedron.
-/
def bcfwChannelNumerator
    (amplitudeLeft amplitudeRight : ℂ) : ℂ :=
  amplitudeLeft * amplitudeRight

/-- A scalar model for one factorization-channel contribution. -/
def bcfwChannelTerm
    (amplitudeLeft amplitudeRight propagator : ℂ) : ℂ :=
  bcfwChannelNumerator amplitudeLeft amplitudeRight / propagator

theorem bcfw_channel_term_eq
    (amplitudeLeft amplitudeRight propagator : ℂ) :
    bcfwChannelTerm
        amplitudeLeft amplitudeRight propagator =
      amplitudeLeft * amplitudeRight / propagator := by
  rfl

end

end InfoGeometry.Canonical
