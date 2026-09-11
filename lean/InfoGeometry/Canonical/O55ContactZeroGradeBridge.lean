import InfoGeometry.Orthogonal.O55ContactZeroGrade
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Canonical publication bridge for the existing degree-zero `O(5,5)` contact
generators.  The full contact/TKK identification is intentionally separate. -/

namespace InfoGeometry.Canonical.O55ContactZeroGradeBridge

open InfoGeometry.Orthogonal.O55Contact

theorem zero_grade_structure
    (a b c d : Outer2) (u v w z : Middle6) :
    ⁅outerZeroGenerator a b, middleZeroGenerator u v⁆ = 0 ∧
      ⁅outerZeroGenerator a b, outerZeroGenerator c d⁆ =
        outerPairing b c • outerZeroGenerator a d -
          outerPairing a d • outerZeroGenerator c b ∧
      ⁅middleZeroGenerator u v, middleZeroGenerator w z⁆ =
        middlePairing v w • middleZeroGenerator u z -
        middlePairing u w • middleZeroGenerator v z -
        middlePairing v z • middleZeroGenerator u w +
        middlePairing u z • middleZeroGenerator v w :=
  zero_grade_structure_packet a b c d u v w z

end InfoGeometry.Canonical.O55ContactZeroGradeBridge
