import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Canonical.UHFCohomologyColimit

/-!
# Finite-dimensional Cuntz-induction bridge for the split-octonion Peirce pair

This module is the Lean twin of
`tools/sympy/split_octonion_cuntz_induction_bridge.py`.

#### BUCKET 1: CLOSED FINITE THEOREMS

This file proves only finite Peirce projection and compression facts:

* `ePlus` and `eMinus` are idempotent and mutually annihilating projections in
  the concrete Zorn multiplication table;
* their coordinatewise sum is the finite diagonal unit `oneZ`;
* same-index Witt products recover those two Peirce projections;
* the finite projection-compression map `X ↦ e₊ X e₊ + e₋ X e₋` fixes the
  diagonal Peirce sector and kills the off-diagonal Witt slots;
* the repository's abstract finite UHF transition formula reduces to ordinary
  projection compression when its two branch elements are self-adjoint.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The generic UHF formula theorem assumes only explicit `Ring`/`StarRing`
premises and the two named self-adjointness hypotheses on `S_L` and `S_R`.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here constructs a Cuntz `O₂` representation of split octonions,
proves a C*-completion, proves UHF inductive-limit existence, supplies a Jones
tower, proves Yang-Baxter coherence, derives wallpaper forcing, proves Clifford
volume invariance, or establishes arbitrary q-deformed Casimir preservation.

The bridge connects the split-octonion Peirce/Witt packet to the repository's
finite Cuntz/UHF induction formula only at the projection-compression level.
The abstract UHF formula is

`UHF_transition S_L S_R X = S_L * X * star S_L + S_R * X * star S_R`.

For the concrete Peirce idempotents we record the finite-dimensional shadow

`X ↦ e₊ X e₊ + e₋ X e₋`.

This bridge proves that the formula fixes the diagonal unit and hyperbolic
chiral element, while killing the off-diagonal Witt slots.
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

/-- Left Peirce projection idempotence in the concrete split-octonion table. -/
theorem peirce_left_projection_idempotent : mulZ ePlus ePlus = ePlus :=
  ePlus_idempotent

/-- Right Peirce projection idempotence in the concrete split-octonion table. -/
theorem peirce_right_projection_idempotent : mulZ eMinus eMinus = eMinus :=
  eMinus_idempotent

/-- The two Peirce projections are left-right orthogonal. -/
theorem peirce_left_right_projection_zero : mulZ ePlus eMinus = zeroZ :=
  ePlus_mul_eMinus

/-- The two Peirce projections are right-left orthogonal. -/
theorem peirce_right_left_projection_zero : mulZ eMinus ePlus = zeroZ :=
  eMinus_mul_ePlus

/-- Finite projection partition: the two Peirce idempotents reconstruct the unit. -/
theorem peirce_projection_partition : addZ ePlus eMinus = oneZ := by
  rfl

/-- Same-index upper/lower Witt products recover the left Peirce projection. -/
theorem witt_up_down_projection (i : Fin 3) : mulZ (up i) (down i) = ePlus :=
  up_mul_down_same i

/-- Same-index lower/upper Witt products recover the right Peirce projection. -/
theorem witt_down_up_projection (i : Fin 3) : mulZ (down i) (up i) = eMinus :=
  down_mul_up_same i

/-- Upper Witt slots are left-supported by the left Peirce projection. -/
theorem witt_up_left_support (i : Fin 3) : mulZ ePlus (up i) = up i :=
  ePlus_mul_up i

/-- Upper Witt slots are right-supported by the right Peirce projection. -/
theorem witt_up_right_support (i : Fin 3) : mulZ (up i) eMinus = up i :=
  up_mul_eMinus i

/-- Lower Witt slots are left-supported by the right Peirce projection. -/
theorem witt_down_left_support (i : Fin 3) : mulZ eMinus (down i) = down i :=
  eMinus_mul_down i

/-- Lower Witt slots are right-supported by the left Peirce projection. -/
theorem witt_down_right_support (i : Fin 3) : mulZ (down i) ePlus = down i :=
  down_mul_ePlus i

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
    mulZ ePlus ePlus = ePlus ∧
      mulZ eMinus eMinus = eMinus ∧
      mulZ ePlus eMinus = zeroZ ∧
      mulZ eMinus ePlus = zeroZ ∧
      addZ ePlus eMinus = oneZ ∧
      (∀ i : Fin 3, mulZ (up i) (down i) = ePlus) ∧
      (∀ i : Fin 3, mulZ (down i) (up i) = eMinus) ∧
      peirceCuntzTransition oneZ = oneZ ∧
      peirceCuntzTransition ePlus = ePlus ∧
      peirceCuntzTransition eMinus = eMinus ∧
      peirceCuntzTransition H = H ∧
      (∀ i : Fin 3, peirceCuntzTransition (up i) = zeroZ) ∧
      (∀ i : Fin 3, peirceCuntzTransition (down i) = zeroZ) ∧
      (∀ i : Fin 3, peirceCuntzTransition (commZ (up i) (down i)) = H) ∧
      (∀ i : Fin 3, peirceCuntzTransition (antiCommZ (up i) (down i)) = oneZ) := by
  exact ⟨peirce_left_projection_idempotent, peirce_right_projection_idempotent,
    peirce_left_right_projection_zero, peirce_right_left_projection_zero,
    peirce_projection_partition, witt_up_down_projection, witt_down_up_projection,
    peirceCuntzTransition_oneZ, peirceCuntzTransition_ePlus,
    peirceCuntzTransition_eMinus, peirceCuntzTransition_H,
    peirceCuntzTransition_up_zero, peirceCuntzTransition_down_zero,
    peirceCuntzTransition_comm_up_down, peirceCuntzTransition_anticomm_up_down⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.CuntzInductionBridge
