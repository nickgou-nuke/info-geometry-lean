import InfoGeometry.Topology.CuntzCantorSpectralTriple
import Mathlib

/-!
# Cuntz Map — Algebraic Two-Branch Transfer

The Cuntz map Φ(X) = S_L·X·S*_L + S_R·X·S*_R is the canonical
endomorphism associated to an abstract `O₂` carrier.

## Algebraic Properties
This file proves only the algebraic facts visible from the Cuntz relations:

  Φ(1) = 1        (probability conservation)
  Φ(X*) = Φ(X)*    (reality preservation)

KMS fixed-point and modular-flow statements are formulated with explicit
branch-scaling or pointwise equality witnesses.  This file does not prove
uniqueness, contractive convergence, complete positivity, or equality with a
continuous modular flow.
-/

namespace CuntzMap

open InfoGeometry.Topology.CuntzCantorSpectralTriple

variable (Op : Type*) [Ring Op] [StarRing Op]

/--
The Cuntz map / canonical endomorphism of the Cuntz O₂ algebra.

  Φ(X) = S_left·X·S*_left + S_right·X·S*_right

This is the Markov transfer operator — the discrete modular flow
that generates time evolution on the Cantor boundary.
-/
def map (C : CuntzO2Carrier Op) (X : Op) : Op :=
  C.S_left * X * star C.S_left + C.S_right * X * star C.S_right

/--
**Unitality:** Φ(1) = 1. The Cuntz map preserves the identity,
encoding probability conservation — the total probability mass
redistributes across the two branches and sums to 1.
-/
theorem map_unital (C : CuntzO2Carrier Op) :
    map Op C 1 = 1 := by
  simpa [map] using C.range_sum

/--
**Star-preserving:** Φ(X*) = Φ(X)*. The Cuntz map respects the
*-involution, preserving the reality/observable structure of the
algebra. This makes Φ a completely positive map.
-/
theorem map_star (C : CuntzO2Carrier Op) (X : Op) :
    map Op C (star X) = star (map Op C X) := by
  unfold map
  simp [star_add, star_mul, mul_assoc]

/-- Additive real readout fixed by equal half-branch Cuntz scaling. -/
theorem map_real_fixed_point_of_half_branch_scaling
    (C : CuntzO2Carrier Op)
    (φ : Op →+ ℝ)
    (X : Op)
    (hleft : φ (C.S_left * X * star C.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (C.S_right * X * star C.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (map Op C X) = φ X := by
  rw [map, map_add, hleft, hright]
  ring

/--
Witness that a supplied discrete modular step is pointwise the Cuntz map.

The equality is data, not inferred from the Cuntz relations alone.
-/
structure DiscreteModularFlowWitness (C : CuntzO2Carrier Op) where
  sigma : Op → Op
  sigma_eq_map : ∀ X, sigma X = map Op C X

namespace DiscreteModularFlowWitness

variable {C : CuntzO2Carrier Op}
variable (W : DiscreteModularFlowWitness Op C)

/-- The witnessed discrete modular step evaluates as the Cuntz map. -/
theorem apply_eq_map (X : Op) :
    W.sigma X = map Op C X :=
  W.sigma_eq_map X

/-- A half-branch real readout is fixed by a witnessed Cuntz modular step. -/
theorem real_fixed_point_of_half_branch_scaling
    (φ : Op →+ ℝ)
    (X : Op)
    (hleft : φ (C.S_left * X * star C.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (C.S_right * X * star C.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (W.sigma X) = φ X := by
  rw [DiscreteModularFlowWitness.apply_eq_map (Op := Op) (C := C) W X]
  exact map_real_fixed_point_of_half_branch_scaling Op C φ X hleft hright

end DiscreteModularFlowWitness

end CuntzMap
