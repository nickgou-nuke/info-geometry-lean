import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Algebra.FiveGradedTKK
import InfoGeometry.Canonical.ConformalFiveGradeInversion

/-!
# InfoGeometry.Canonical.O55FiveGradeWeights

Label weights for the O(5,5) five-grade decomposition.

This owner exposes the finite `Weight5` label readout already defined by
`FiveGradedTKK`.  The names below record the intended grade assignment of the
conformal-generator labels; they are not claims about an adjoint action.  A
theorem identifying these labels with an actual adjoint representation would
require a separately defined representation and is intentionally outside this
finite readout owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.O55FiveGradeWeights

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Algebra.FiveGradedTKK
open InfoGeometry.Canonical.ConformalFiveGradeInversion

def weightOf (k : Weight5) : ℤ := Weight5.toInt k

def weight_u5 : ℤ := weightOf Weight5.pos_one
def weight_v5 : ℤ := weightOf Weight5.neg_one
def weight_u4 : ℤ := weightOf Weight5.pos_one
def weight_v4 : ℤ := weightOf Weight5.neg_one
def weight_D5 : ℤ := weightOf Weight5.zero
def weight_D4 : ℤ := weightOf Weight5.zero
def weight_D  : ℤ := weightOf Weight5.zero
def weight_J5 : ℤ := weightOf Weight5.zero
def weight_J4 : ℤ := weightOf Weight5.zero
def weight_J  : ℤ := weightOf Weight5.zero

/- The finite label assignments reduce to the expected integers. -/
theorem weight_constants :
    weight_u5 = 1 ∧ weight_v5 = -1 ∧ weight_u4 = 1 ∧ weight_v4 = -1 ∧
    weight_D5 = 0 ∧ weight_D4 = 0 ∧ weight_D = 0 ∧
    weight_J5 = 0 ∧ weight_J4 = 0 ∧ weight_J = 0 := by
  norm_num [weight_u5, weight_v5, weight_u4, weight_v4, weightOf,
            weight_D5, weight_D4, weight_D,
            weight_J5, weight_J4, weight_J]

end InfoGeometry.Canonical.O55FiveGradeWeights
