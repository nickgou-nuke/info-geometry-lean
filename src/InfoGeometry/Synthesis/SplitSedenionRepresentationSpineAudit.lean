/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SplitSedenionRepresentationSpine

/-!
# Selected Kernel Axiom Diagnostics for `SplitSedenionRepresentationSpine`

Checks selected exported signatures and prints axiom dependencies for selected theorems. These
diagnostics do not enforce an allowed-axiom whitelist and do not cover every declaration in the
source module. Use the repository certification workflow for a complete checked whitelist audit.

The source module's native Clifford `Cl44` Nambu results and its `Matrix (Fin 16) (Fin 16) ℝ`
right-ideal results are separate carrier-level developments; this audit does not assert an
identification or an intertwining map between them.
-/

namespace InfoGeometry.Synthesis.SplitSedenionRepresentationSpineAudit

open InfoGeometry.Synthesis.SplitSedenionRepresentationSpine

#check @IsProductDerivation
#check @transportedProduct
#check @transportOperator
#check @derivation_transport
#check @Intertwines
#check @transport_intertwines
#check @intertwines_comp
#check @productDerivation_commutator
#check @transportOperator_commutator
#check @nambuField44
#check @nambuMajoranaPlus
#check @nambuMajoranaMinus
#check @nambuMajoranaPlus_eq_e
#check @nambuMajoranaMinus_eq_f
#check @nambuMajoranaPlus_sq
#check @nambuMajoranaMinus_sq
#check @nambuMajorana_anticomm
#check @cl44VacuumIdempotent_right_annihilated
#check @nambuLeftIdealGen
#check @nambuRightIdealGen
#check @nambuLeftIdealGen_mem_leftIdeal
#check @nambuRightIdealGen_mem_rightIdeal
#check @nambuRightIdealGen_mul_nambuLeftIdealGen
#check @RightIdeal
#check @rightIdealEquiv
#check @leftIdealBasisMat
#check @rightIdealBasisMat
#check @rightIdealBasisMat_mul_leftIdealBasisMat
#check @leftRightDyad_mul_leftIdealBasisMat

#print axioms derivation_transport
#print axioms transport_intertwines
#print axioms intertwines_comp
#print axioms productDerivation_commutator
#print axioms transportOperator_commutator
#print axioms nambuMajoranaPlus_eq_e
#print axioms nambuMajoranaMinus_eq_f
#print axioms nambuMajoranaPlus_sq
#print axioms nambuMajoranaMinus_sq
#print axioms nambuMajorana_anticomm
#print axioms cl44VacuumIdempotent_right_annihilated
#print axioms nambuRightIdealGen_mul_nambuLeftIdealGen
#print axioms rightIdealEquiv
#print axioms rightIdealBasisMat_mul_leftIdealBasisMat
#print axioms leftRightDyad_mul_leftIdealBasisMat

end InfoGeometry.Synthesis.SplitSedenionRepresentationSpineAudit
