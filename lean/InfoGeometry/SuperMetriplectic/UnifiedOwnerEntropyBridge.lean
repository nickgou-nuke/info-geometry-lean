import InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge
import InfoGeometry.SuperMetriplectic.EntropyShadowBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Unified Owner Entropy Bridge

Bridge from the operator-to-body compatibility packet into the existing
coadjoint-leaf/body-entropy split language.

This file stays fully honest:

* no new entropy law is proved from operator theory,
* no canonical probe is invented,
* the existing scalar body-entropy packet is simply re-exported through the
  new operator-to-triad compatibility layer.
-/

namespace UnifiedOwnerEntropyBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge
open InfoGeometry.SuperMetriplectic.EntropyShadowBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace UnifiedOwnerTriadCompatibility

variable (C : UnifiedOwnerTriadCompatibility (E := E))

/--
The operator-to-body compatibility packet carries the same coadjoint-leaf
entropy split as its scalar body-entropy packet.
-/
@[rep_depth transport]
def toCoadjointLeafEntropySplit :
    InfoGeometry.SuperMetriplectic.CoadjointLeafEntropySplit :=
  InfoGeometry.SuperMetriplectic.EntropyShadowBridge.toCoadjointLeafEntropySplit C.triad.entropy

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction :
    (toCoadjointLeafEntropySplit C).totalEntropyChange = C.triad.entropy.production := by
  exact
    InfoGeometry.SuperMetriplectic.EntropyShadowBridge.toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction
      C.triad.entropy

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_totalEntropyChange_nonnegative :
    0 ≤ (toCoadjointLeafEntropySplit C).totalEntropyChange := by
  exact (toCoadjointLeafEntropySplit C).totalEntropyChange_nonnegative

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_leafEntropyChange_eq_zero :
    (toCoadjointLeafEntropySplit C).leafEntropyChange = 0 := by
  exact (toCoadjointLeafEntropySplit C).leaf_entropy_change_zero

@[rep_depth transport]
theorem toCoadjointLeafEntropySplit_transverseEntropyProduction_nonnegative :
    0 ≤ (toCoadjointLeafEntropySplit C).transverseEntropyProduction := by
  exact (toCoadjointLeafEntropySplit C).transverse_entropy_nonnegative

/--
Combined capstone packet for the entropy side of the operator-to-body bridge.
-/
@[capstone, rep_depth transport]
theorem ownerEntropyBridge_packet :
    ((toCoadjointLeafEntropySplit C).leafEntropyChange = 0)
      ∧
    (0 ≤ (toCoadjointLeafEntropySplit C).transverseEntropyProduction)
      ∧
    ((toCoadjointLeafEntropySplit C).totalEntropyChange = C.triad.entropy.production)
      ∧
    (0 ≤ (toCoadjointLeafEntropySplit C).totalEntropyChange) := by
  refine ⟨toCoadjointLeafEntropySplit_leafEntropyChange_eq_zero (C := C), ?_, ?_, ?_⟩
  · exact toCoadjointLeafEntropySplit_transverseEntropyProduction_nonnegative (C := C)
  · exact toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction (C := C)
  · exact toCoadjointLeafEntropySplit_totalEntropyChange_nonnegative (C := C)

end UnifiedOwnerTriadCompatibility

end Core

end UnifiedOwnerEntropyBridge
