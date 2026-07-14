import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Algebra.FiveGradedTKK
import InfoGeometry.Canonical.ConformalFiveGradeInversion

/-!
# InfoGeometry.Canonical.O55FiveGradeWeights

Constant weights for the O(5,5) five-grade decomposition,
matching the JSON output from `tools/infra/o55_fivegrade_weights.py`.

This file provides the integer weights as Lean constants.
The relationship to the adjoint actions of D is described in the
comments; formal proofs of those relationships are left as future work.
-/

noncomputable section

namespace O55FiveGradeWeights

open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Algebra.FiveGradedTKK
open InfoGeometry.Canonical.ConformalFiveGradeInversion

-- Weight constants (matching the Python script output)
def weight_u5 : ℤ := 1
def weight_v5 : ℤ := -1
def weight_u4 : ℤ := 1
def weight_v4 : ℤ := -1
def weight_D5 : ℤ := 0
def weight_D4 : ℤ := 0
def weight_D  : ℤ := 0
def weight_J5 : ℤ := 0
def weight_J4 : ℤ := 0
def weight_J  : ℤ := 0

-- Trivial theorem that the constants have the expected values.
theorem weight_constants :
    weight_u5 = 1 ∧ weight_v5 = -1 ∧ weight_u4 = 1 ∧ weight_v4 = -1 ∧
    weight_D5 = 0 ∧ weight_D4 = 0 ∧ weight_D = 0 ∧
    weight_J5 = 0 ∧ weight_J4 = 0 ∧ weight_J = 0 := by
  norm_num [weight_u5, weight_v5, weight_u4, weight_v4,
            weight_D5, weight_D4, weight_D,
            weight_J5, weight_J4, weight_J] <;> rfl

end O55FiveGradeWeights