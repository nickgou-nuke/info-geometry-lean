import InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge
import InfoGeometry.Topology.KleinRealOperatorDescent

/-! Seam compatibility uses the existing Klein involution and literal torus
orbit quotient. Fixedness is an algebraic descent condition, not a definition
of continuity. The coefficient is forced to be odd only when the state can
be cancelled; none of these statements forces a nonzero mass or spectral gap. -/

namespace InfoGeometry.Synthesis.KleinDiracKahler

open InfoGeometry.Canonical.KleinBottleTwistedCommutant
open InfoGeometry.Topology.KleinRealOperatorDescent
open KleinBrillouinBase KleinBottleOrbitQuotient

variable {A : Type*} [Ring A]

theorem equation_covariant
    (twist : A →+* A) (difference coefficient phase state : A)
    (difference_fixed : twist difference = difference)
    (coefficient_odd : twist coefficient = -coefficient)
    (phase_odd : twist phase = -phase)
    (equation : difference * state = coefficient * state * phase) :
    difference * twist state = coefficient * twist state * phase := by
  simpa only [map_mul, difference_fixed, coefficient_odd, phase_odd,
    neg_mul, mul_neg, neg_neg] using congrArg twist equation

theorem equation_covariant_iff
    (twist : A ≃+* A) (difference coefficient phase state : A)
    (difference_fixed : twist difference = difference)
    (coefficient_odd : twist coefficient = -coefficient)
    (phase_odd : twist phase = -phase) :
    difference * twist state = coefficient * twist state * phase ↔
      difference * state = coefficient * state * phase := by
  constructor
  · intro equation
    apply twist.injective
    simpa only [map_mul, difference_fixed, coefficient_odd, phase_odd,
      neg_mul, mul_neg, neg_neg] using equation
  · exact equation_covariant twist.toRingHom difference coefficient phase state
      difference_fixed coefficient_odd phase_odd

theorem fixed_product_iff_coefficient_odd
    (twist : A →+* A) (coefficient phase : A)
    (phase_square : phase * phase = -1)
    (phase_odd : twist phase = -phase) :
    twist (coefficient * phase) = coefficient * phase ↔
      twist coefficient = -coefficient := by
  constructor
  · intro fixed
    have cancelled := congrArg (fun value => value * phase) fixed
    rw [map_mul, phase_odd] at cancelled
    simpa [mul_assoc, neg_mul, mul_neg, phase_square] using cancelled
  · intro odd
    rw [map_mul, odd, phase_odd, neg_mul_neg]

theorem seam_equation_product_odd
    (twist : KleinInvolution A) (derivative coefficient state phase : A)
    (phase_square : phase * phase = -1)
    (phase_odd : twist.toRingAut phase = -phase)
    (equation : derivative = coefficient * state * phase)
    (derivative_fixed : twist.toRingAut derivative = derivative) :
    twist.toRingAut (coefficient * state) = -(coefficient * state) := by
  apply (fixed_product_iff_coefficient_odd twist.toRingAut.toRingHom
    (coefficient * state) phase phase_square phase_odd).mp
  simpa only [← equation] using derivative_fixed

theorem seam_equation_coefficient_odd
    (twist : KleinInvolution A) (derivative coefficient state phase : A)
    (phase_square : phase * phase = -1)
    (phase_odd : twist.toRingAut phase = -phase)
    (equation : derivative = coefficient * state * phase)
    (derivative_fixed : twist.toRingAut derivative = derivative)
    (state_fixed : twist.toRingAut state = state)
    (state_unit : IsUnit state) :
    twist.toRingAut coefficient = -coefficient := by
  apply state_unit.mul_right_cancel
  have product_odd := seam_equation_product_odd twist derivative coefficient
    state phase phase_square phase_odd equation derivative_fixed
  simpa only [map_mul, state_fixed, neg_mul] using product_odd

theorem zero_coefficient_compatible (twist : KleinInvolution A) (state phase : A) :
    (0 : A) = 0 * state * phase ∧ twist.toRingAut (0 : A) = -(0 : A) := by
  simp

section RealFields

variable [Algebra ℝ A]

theorem signed_coupling_invariant
    (coefficient state phase : BrillouinTorus → A)
    (coefficient_odd : ∀ point, coefficient (torusGlide point) = -coefficient point)
    (state_fixed : ∀ point, state (torusGlide point) = state point)
    (phase_odd : ∀ point, phase (torusGlide point) = -phase point) :
    (fun point => coefficient point * state point * phase point) ∈
      invariantFields := by
  intro point
  simp only [coefficient_odd, state_fixed, phase_odd, neg_mul, mul_neg, neg_neg]

noncomputable def descendedCoupling
    (coefficient state phase : BrillouinTorus → A)
    (coefficient_odd : ∀ point, coefficient (torusGlide point) = -coefficient point)
    (state_fixed : ∀ point, state (torusGlide point) = state point)
    (phase_odd : ∀ point, phase (torusGlide point) = -phase point) :
    KleinBrillouinQuotient → A :=
  fieldEquiv.symm ⟨fun point => coefficient point * state point * phase point,
    signed_coupling_invariant coefficient state phase coefficient_odd state_fixed phase_odd⟩

@[simp] theorem descendedCoupling_apply
    (coefficient state phase : BrillouinTorus → A)
    (coefficient_odd : ∀ point, coefficient (torusGlide point) = -coefficient point)
    (state_fixed : ∀ point, state (torusGlide point) = state point)
    (phase_odd : ∀ point, phase (torusGlide point) = -phase point)
    (point : BrillouinTorus) :
    descendedCoupling coefficient state phase coefficient_odd state_fixed phase_odd
        (quotientMap point) = coefficient point * state point * phase point := rfl

end RealFields

end InfoGeometry.Synthesis.KleinDiracKahler
