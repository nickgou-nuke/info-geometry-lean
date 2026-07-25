import Mathlib.Tactic
import InfoGeometry.Canonical.CantorKMSCylinderState

/-!
# Cantor cylinder priors

This file turns the existing finite-cylinder KMS recursion into an explicit
Bayesian-style prior on binary prefixes.

The only theorem content here is finite and exact:
* the uniform cylinder weight is nonnegative;
* it satisfies successor consistency across the two child cylinders;
* therefore it is a finitely additive prefix prior on the binary tape.

No global measure-theoretic extension is claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderPrior

open InfoGeometry.Canonical.CantorKMSCylinderState
open InfoGeometry.Canonical.CantorCuntzBasis

/-- The binary prefix type used by the Cantor cylinder prior. -/
abbrev BinaryWord := InfoGeometry.Canonical.CantorCuntzBasis.BinaryWord

/-- A finite binary cylinder prior on tape prefixes. -/
structure CylinderPrior where
  weight : BinaryWord → ℝ
  nonneg : ∀ w, 0 ≤ weight w
  successor_consistent : ∀ w, weight (false :: w) + weight (true :: w) = weight w

/-- The uniform KMS cylinder weight is a concrete cylinder prior. -/
def uniformKMSPrior : CylinderPrior where
  weight := cylinderKMSWeight
  nonneg := cylinderKMSWeight_nonneg
  successor_consistent := cylinderKMSWeight_children_sum

theorem uniformKMSPrior_weight_nonneg (w : BinaryWord) :
    0 ≤ uniformKMSPrior.weight w := by
  simpa [uniformKMSPrior] using uniformKMSPrior.nonneg w

theorem uniformKMSPrior_successor_consistent (w : BinaryWord) :
    uniformKMSPrior.weight (false :: w) + uniformKMSPrior.weight (true :: w) =
      uniformKMSPrior.weight w := by
  simpa [uniformKMSPrior] using uniformKMSPrior.successor_consistent w

/-- The uniform KMS prior is finitely additive at each binary refinement step. -/
theorem uniformKMSPrior_finitely_additive (w : BinaryWord) :
    uniformKMSPrior.weight w =
      uniformKMSPrior.weight (false :: w) + uniformKMSPrior.weight (true :: w) := by
  symm
  exact uniformKMSPrior_successor_consistent w

end InfoGeometry.Canonical.CantorCylinderPrior
