import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Core.Jordan
import InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional
import InfoGeometry.Quantum.SplitTrialityKernel

/-!
# Split-Octonion Taming Bridge

This module records the theorem-safe interpretation of the "split-octonion"
frontier in the current repository.

There is no repo-owned literal nonassociative split-octonion multiplication
surface here. Instead, the supported lanes are:

* split Bott/Clifford shadow: `Cl(4,4)` in `Clifford.BottPeriodicity`;
* Jordan taming: symmetric product laws in `Core.Jordan`;
* split triality: nilpotent chiral channels in `Quantum.SplitTrialityKernel`;
* Drazin information extraction: regular/stable versus singular/residue data in
  `OperatorAlgebra.DrazinEntropyFunctional`.

So this file deliberately does not try to make split-octonions into a
`DivisionRing`, and it does not invent octonionic multiplication. It only
exposes the supported "banished or tamed by pairing" chain.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionTamingBridge

open scoped InfoGeometryJordan

/-! ## Split Bott / Clifford shadow -/

/--
The repo-supported split-octonion shadow is the split `Cl(4,4)` object in the
Bott tower, not a literal nonassociative octonion multiplication.
-/
@[rep_depth krein]
abbrev SplitOctonionCliffordShadow :=
  InfoGeometry.Clifford.BottPeriodicity.Cl44

/-- Carrier of the split `Cl(4,4)` shadow. -/
@[rep_depth krein]
abbrev SplitOctonionCarrierShadow :=
  InfoGeometry.Clifford.BottPeriodicity.Carrier44

/--
`Cl(4,4)` is represented by the existing split Bott step over `Cl(3,3)`.
-/
@[rep_depth krein]
theorem splitOctonionCliffordShadow_eq_splitBottOwner :
    InfoGeometry.Clifford.BottPeriodicity.cl44_as_splitBottStep =
      InfoGeometry.CliffordTower.clsplit_succ_equiv 3 :=
  InfoGeometry.Clifford.BottPeriodicity.cl44_as_splitBottStep_eq_owner

/-! ## Jordan taming -/

section Jordan

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [InfoGeometry.Core.JordanAlgebra V]

/--
Jordan taming keeps the symmetric product in the formally supported lane.
This is the repository-owned Jordan identity.
-/
theorem jordan_taming_identity
    (x y : V) :
    (x ⊙ x) ⊙ (x ⊙ y) = x ⊙ ((x ⊙ x) ⊙ y) :=
  InfoGeometry.Core.jordan_prod_identity x y

/-- The tamed Jordan product is commutative. -/
theorem jordan_taming_comm
    (x y : V) :
    x ⊙ y = y ⊙ x :=
  InfoGeometry.Core.jordan_prod_comm x y

end Jordan

/-! ## Split triality nilpotent channels -/

section Triality

/-- The left chiral triality channel is nilpotent. -/
@[rep_depth krein]
theorem splitTriality_left_channel_nilpotent
    (T : InfoGeometry.Quantum.SplitTrialityKernel) :
    T.vectorToLeftSpinor.comp T.vectorToLeftSpinor = 0 :=
  T.left_nilpotent

/-- The right chiral triality channel is nilpotent. -/
@[rep_depth krein]
theorem splitTriality_right_channel_nilpotent
    (T : InfoGeometry.Quantum.SplitTrialityKernel) :
    T.vectorToRightSpinor.comp T.vectorToRightSpinor = 0 :=
  T.right_nilpotent

/-- The paired triality supercharge squares to the identity. -/
@[rep_depth krein]
theorem splitTriality_paired_supercharge_sq_eq_id
    (T : InfoGeometry.Quantum.SplitTrialityKernel) :
    T.trialitySupercharge.comp T.trialitySupercharge = LinearMap.id :=
  T.trialitySupercharge_sq_eq_id

end Triality

/-! ## Drazin information extraction boundary -/

section DrazinInformation

variable {Op State : Type*}
variable (P : InfoGeometry.OperatorAlgebra.DrazinInformationExtraction Op State)

/--
The stable-information readout is the Drazin regular part on admissible states.
In the split-octonion interpretation, this is the stable associative/tamed
readout side.
-/
theorem stableInformation_eq_regularPart_on_state
    (s : State) (h_state : P.readout.valid s) :
    P.stableInformation s = P.readout.regularPart s :=
  P.stableInformation_eq_regularPart s h_state

/--
The singular-residue readout is the Drazin nilpotent residue on admissible
states. In the split-octonion interpretation, this is where null/nilpotent
defect data are retained.
-/
theorem singularResidue_eq_nilpotentResidue_on_state
    (s : State) (h_state : P.readout.valid s) :
    P.singularResidue s = P.readout.nilpotentResidue s :=
  P.singularResidue_eq_nilpotentResidue s h_state

end DrazinInformation

end InfoGeometry.Canonical.SplitOctonionTamingBridge
