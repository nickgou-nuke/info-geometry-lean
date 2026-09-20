import InfoGeometry.Synthesis.KleinDiracKahler

namespace InfoGeometry.Synthesis.KleinDiracKahlerTests

open InfoGeometry.Synthesis.KleinDiracKahler
open InfoGeometry.Canonical.KleinBottleTwistedCommutant
open InfoGeometry.Topology.KleinRealOperatorDescent
open KleinBrillouinBase KleinBottleOrbitQuotient

variable {A : Type*} [Ring A]

example (twist : KleinInvolution A) (difference coefficient phase state : A)
    (difference_fixed : twist.toRingAut difference = difference)
    (coefficient_odd : twist.toRingAut coefficient = -coefficient)
    (phase_odd : twist.toRingAut phase = -phase) :
    difference * twist.toRingAut state = coefficient * twist.toRingAut state * phase ↔
      difference * state = coefficient * state * phase :=
  equation_covariant_iff twist.toRingAut difference coefficient phase state
    difference_fixed coefficient_odd phase_odd

example (cycle phase : A) (reversed : cycle * phase = -(phase * cycle)) :
    cycle * cycle * phase = phase * (cycle * cycle) :=
  InfoGeometry.Canonical.DiscreteDiracHodgeChiral.square_commutes_chirality_of_anticommutes
    cycle phase reversed

example (twist : KleinInvolution A) (derivative coefficient phase : A)
    (square : phase * phase = -1) (reversed : twist.toRingAut phase = -phase)
    (equation : derivative = coefficient * phase)
    (fixed : twist.toRingAut derivative = derivative) :
    twist.toRingAut coefficient = -coefficient := by
  exact seam_equation_coefficient_odd twist derivative coefficient 1 phase
    square reversed (by simpa using equation) fixed (map_one _) isUnit_one

example (twist : KleinInvolution A) (state phase : A) :
    (0 : A) = 0 * state * phase ∧ twist.toRingAut (0 : A) = -(0 : A) :=
  zero_coefficient_compatible twist state phase

example (twist : KleinInvolution A) (coefficient phase : A) :
    twist.toRingAut (coefficient * 0 * phase) = coefficient * 0 * phase := by
  simp

example [Algebra ℝ A] (field : KleinBrillouinQuotient → A)
    (point : BrillouinTorus) :
    fieldEquiv field (torusGlide point) = fieldEquiv field point :=
  (fieldEquiv field).property point

#print axioms fixed_product_iff_coefficient_odd
#print axioms equation_covariant
#print axioms equation_covariant_iff
#print axioms seam_equation_coefficient_odd
#print axioms descendedCoupling_apply
#print axioms quotient_dirac_square

end InfoGeometry.Synthesis.KleinDiracKahlerTests
