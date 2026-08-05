import Mathlib.Tactic
import InfoGeometry.Canonical.CantorKMSCylinderState

/-!
# Native Cantor cylinder prior identities

The finite prefix weight is the existing native KMS cylinder weight. This owner
proves its positivity and binary refinement additivity directly.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderPrior

open InfoGeometry.Canonical.CantorKMSCylinderState
open InfoGeometry.Canonical.CantorCuntzBasis

abbrev BinaryWord := InfoGeometry.Canonical.CantorCuntzBasis.BinaryWord

theorem cylinderKMSWeight_nonnegative (w : BinaryWord) :
    0 ≤ cylinderKMSWeight w :=
  cylinderKMSWeight_nonneg w

theorem cylinderKMSWeight_finitely_additive (w : BinaryWord) :
    cylinderKMSWeight w =
      cylinderKMSWeight (false :: w) + cylinderKMSWeight (true :: w) := by
  symm
  exact cylinderKMSWeight_children_sum w

end InfoGeometry.Canonical.CantorCylinderPrior
