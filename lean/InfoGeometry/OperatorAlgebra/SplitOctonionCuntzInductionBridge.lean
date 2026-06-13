import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Canonical.UHFCohomologyColimit

/-!
# Finite-dimensional Cuntz-induction bridge for the split-octonion Peirce pair

This module is the Lean twin of
`tools/sympy/split_octonion_cuntz_induction_bridge.py`.

It connects the split-octonion Peirce/Witt packet to the repository's finite
Cuntz/UHF induction formula only at the projection-compression level.  The
abstract UHF formula is

`UHF_transition S_L S_R X = S_L * X * star S_L + S_R * X * star S_R`.

For the concrete Peirce idempotents we record the finite-dimensional shadow

`X ↦ e₊ X e₊ + e₋ X e₋`.

This bridge proves that the formula fixes the diagonal unit and hyperbolic
chiral element, while killing the off-diagonal Witt slots.  It does not assert
that the split-octonion algebra carries Cuntz `O₂` isometries, a C*-completion,
a braid representation, or a wallpaper forcing theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.CuntzInductionBridge

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation

/-- Projection-compression shadow of the two-branch finite Cuntz/UHF transition. -/
def peirceCuntzTransition (X : SplitOct) : SplitOct :=
  addZ (mulZ (mulZ ePlus X) ePlus) (mulZ (mulZ eMinus X) eMinus)

/-- The generic UHF transition reduces to projection compression for self-adjoint branches. -/
theorem UHF_transition_selfadjoint_projection_formula
    {A : Type*} [Ring A] [StarRing A]
    (S_L S_R X : A)
    (hL : star S_L = S_L) (hR : star S_R = S_R) :
    InfoGeometry.Canonical.UHFCohomology.UHF_transition S_L S_R X =
      S_L * X * S_L + S_R * X * S_R := by
  simp [InfoGeometry.Canonical.UHFCohomology.UHF_transition, hL, hR]

/-- The Peirce compression is exactly the split-octonion specialization of that formula. -/
theorem peirceCuntzTransition_eq_projection_formula (X : SplitOct) :
    peirceCuntzTransition X =
      addZ (mulZ (mulZ ePlus X) ePlus) (mulZ (mulZ eMinus X) eMinus) := by
  rfl

/-- Finite Cuntz projection partition: the two Peirce idempotents reconstruct the unit. -/
theorem peirce_projection_partition : addZ ePlus eMinus = oneZ := by
  rfl

/-- The finite transition fixes the diagonal unit. -/
theorem peirceCuntzTransition_oneZ : peirceCuntzTransition oneZ = oneZ := by
  rfl

/-- The finite transition fixes the left Peirce projection. -/
theorem peirceCuntzTransition_ePlus : peirceCuntzTransition ePlus = ePlus := by
  rfl

/-- The finite transition fixes the right Peirce projection. -/
theorem peirceCuntzTransition_eMinus : peirceCuntzTransition eMinus = eMinus := by
  rfl

/-- The finite transition fixes the hyperbolic grading element. -/
theorem peirceCuntzTransition_H : peirceCuntzTransition H = H := by
  rfl

/-- The finite transition kills every upper off-diagonal Witt slot. -/
theorem peirceCuntzTransition_up_zero (i : Fin 3) :
    peirceCuntzTransition (up i) = zeroZ := by
  fin_cases i <;> rfl

/-- The finite transition kills every lower off-diagonal Witt slot. -/
theorem peirceCuntzTransition_down_zero (i : Fin 3) :
    peirceCuntzTransition (down i) = zeroZ := by
  fin_cases i <;> rfl

/-- The Peirce-Witt commutator is stable under the finite transition. -/
theorem peirceCuntzTransition_comm_up_down (i : Fin 3) :
    peirceCuntzTransition (commZ (up i) (down i)) = H := by
  rw [up_down_comm_eq_H]
  exact peirceCuntzTransition_H

/-- The Peirce-Witt anticommutator is stable under the finite transition. -/
theorem peirceCuntzTransition_anticomm_up_down (i : Fin 3) :
    peirceCuntzTransition (antiCommZ (up i) (down i)) = oneZ := by
  rw [up_down_anticomm_eq_oneZ]
  exact peirceCuntzTransition_oneZ

/-- Closed finite-dimensional Cuntz-induction bridge packet. -/
theorem splitOctonion_cuntz_induction_bridge_packet :
    peirceCuntzTransition oneZ = oneZ ∧
      peirceCuntzTransition ePlus = ePlus ∧
      peirceCuntzTransition eMinus = eMinus ∧
      peirceCuntzTransition H = H ∧
      (∀ i : Fin 3, peirceCuntzTransition (up i) = zeroZ) ∧
      (∀ i : Fin 3, peirceCuntzTransition (down i) = zeroZ) ∧
      (∀ i : Fin 3, peirceCuntzTransition (commZ (up i) (down i)) = H) ∧
      (∀ i : Fin 3, peirceCuntzTransition (antiCommZ (up i) (down i)) = oneZ) := by
  exact ⟨peirceCuntzTransition_oneZ, peirceCuntzTransition_ePlus,
    peirceCuntzTransition_eMinus, peirceCuntzTransition_H,
    peirceCuntzTransition_up_zero, peirceCuntzTransition_down_zero,
    peirceCuntzTransition_comm_up_down, peirceCuntzTransition_anticomm_up_down⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.CuntzInductionBridge
