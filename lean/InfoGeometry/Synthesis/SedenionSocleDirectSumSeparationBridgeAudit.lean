/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

/-!
# Audit: `SedenionSocleDirectSumSeparationBridge`

Typecheck and signature audit for `InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge`.
-/

namespace InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge.Audit

open InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

#check @sl2GenJ12Real
#check @sl2GenK13Real
#check @sl2Gen_real_noncommute
#check @socleDerivation_scalar
#check @IsSo21Adjoint
#check @sl2GenJ12_isSo21Adjoint
#check @sl2GenK13_isSo21Adjoint
#check @sl2GenK23_isSo21Adjoint
#check @sl2Gen_isSo21Adjoint
#check @socleDerivation_leibniz_of_isSo21Adjoint
#check @isSo21Adjoint_of_socleDerivation_leibniz
#check @socleDerivation_leibniz_iff_isSo21Adjoint
#check @splitQuatSocleMul
#check @splitQuatSocleMul_assoc
#check @socleDerivation_leibniz_splitQuatSocleMul_of_isSo21Adjoint
#check @embedSplitQuatToZorn
#check @embedSplitQuatToZorn_one
#check @embedSplitQuatToZorn_mul
#check @parameterAction_add
#check @zornG2Derivation_add_left
#check @sedenionG2Derivation_add_left
#check @sedenion_derivations_add
#check @lambda1Probe
#check @socleVectorRead
#check @socleVectorWrite
#check @socleDerivationLift
#check @socleDerivationLift_zero
#check @sedenionMul_lambda1Probe_mul
#check @socleDerivationLift_leibniz_rhs
#check @socleDerivationLift_leibniz_lhs_ne_zero
#check @socleDerivationLift_not_leibniz
#check @sedenionMul_lambda1Probe_mul_10
#check @sedenionMul_lambda1Probe_mul_21
#check @sedenionMul_lambda1Probe_mul_02
#check @socleDerivationLift_leibniz_forces_basis_zero
#check @socleDerivationLift_leibniz_iff_eq_zero
#print axioms socleDerivationLift_leibniz_iff_eq_zero
#check @sedenionSocleDirectSum
#check @sedenionAdd_left_cancel
#check @sedenionSocleDirectSum_K13_not_leibniz
#print axioms sedenionSocleDirectSum_K13_not_leibniz
#check @g2Probe
#check @readSedenionG2Params_socleDerivationLift
#check @readSedenionG2Params_sedenionSocleDirectSum
#check @socleDerivationLift_eq_zero_iff
#check @sedenionSocleDirectSum_injective
#check @sedenionSocleDirectSum_eq_zeroFunction
#check @nonSeparatingMatrix
#check @nonSeparatingMatrix_ne_zero
#check @two_probes_do_not_separate

end InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge.Audit
