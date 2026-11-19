/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom and Integrity Audit for `ExceptionalZornSuperBraidedDerivationBridge`

Verifies via both explicit `#print axioms` on key F8.1–F8.4 declarations and
environment-wide `Lean.Util.CollectAxioms` traversal that every declaration in
`InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge` depends only
on the standard foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`, with zero `sorryAx`, custom axioms, `unsafe`, or `partial`.
-/

section ExplicitPrintAxioms

open InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge

-- F8.4 Spine Helpers
#print axioms inducedActionLaneOnsagerSystem
#print axioms inducedActionLaneOnsagerSystem_totalGenerator
#print axioms onsager_pairing_actionForm_reciprocity_module

-- F8.1 G2DerivationLieAlgebra & CrossProdCarrier
#print axioms g2DerivationEquivIntDerivations
#print axioms g2DerivationEquivIntDerivations_bracket
#print axioms linearG2DerivationEquivDerivations
#print axioms crossProdCarrierDerivationLieLane
#print axioms crossProdCarrier_onsager_reciprocity

-- F8.1 ZornVectorMatrix, ZornMatrix, G2ToBraidChain, & SplitCayley
#print axioms zornVectorMatrixDerivationEquivDerivations
#print axioms zornVectorMatrixDerivationEquivDerivations_bracket
#print axioms zornVectorMatrix_onsager_reciprocity
#print axioms g2ToBraidDerivationEquivCanonicalZorn
#print axioms splitCayleyG2DerivationEquivCanonicalZorn
#print axioms splitCayleyLinearDerivationEquivCanonicalZorn
#print axioms canonicalZornDerivationsToIntDerivations
#print axioms splitCayleyDerivationEquivIntDerivations
#print axioms canonicalZornDerivationsEquivVectorDerivations_lie
#print axioms canonicalZornDerivationsEquivCarrier
#print axioms canonicalZornAction_onsager_reciprocity
#print axioms zornMatrixCarrier_onsager_reciprocity
#print axioms canonicalZornOperator_onsager_reciprocity

-- F8.1 G2H3ZornEntrywiseEmbedding & H3ZornF4Derivations
#print axioms h3ZornJordanDerivation_iff_isLeibniz
#print axioms h3ZornF4DerivationsEquivDerivations
#print axioms g2EntrywiseActionLane
#print axioms compatibleG2ToH3ZornDerivationLieHom_injective
#print axioms compatibleG2H3ZornDerivationLane
#print axioms h3ZornF4DerivationLane
#print axioms g2Entrywise_onsager_reciprocity
#print axioms compatibleG2H3Zorn_onsager_reciprocity
#print axioms h3ZornF4_onsager_reciprocity

-- F8.1 SplitOctonionDerivationAutomorphism
#print axioms splitOctonionDerivationEquivDerivations
#print axioms splitOctonionDerivationEquivDerivations_zero
#print axioms splitOctonionDerivationEquivDerivations_add
#print axioms splitOctonionDerivationEquivDerivations_smul
#print axioms splitOctonionDerivationEquivDerivations_bracket
#print axioms splitOctonionZornDerivationLieLane
#print axioms splitOctonionZornActionLane
#print axioms splitOctonionZorn_onsager_reciprocity
#print axioms splitOctonionZornAction_onsager_reciprocity

-- F8.1 NCZorn & OpZorn
#print axioms ncZornDerivationEquivIntDerivations
#print axioms ncZornDerivationLieLane
#print axioms ncZornRealDerivationEquiv
#print axioms ncZornRealDerivationLieLane
#print axioms ncZornRealOnsagerSystem
#print axioms ncZornReal_onsager_reciprocity
#print axioms opDerivationEquivComplexDerivations
#print axioms opDerivationEquivComplexDerivations_zero
#print axioms opDerivationEquivComplexDerivations_add
#print axioms opDerivationEquivComplexDerivations_smul
#print axioms opDerivationEquivComplexDerivations_commutator
#print axioms opDerivationToRealDerivations_injective
#print axioms opZornRealDerivationLieLane
#print axioms opZornReal_onsager_reciprocity

-- F8.1 AlbertDerivationsF4 JordanDerivation
#print axioms jordanDerivation_isLeibniz
#print axioms jordanDerivationEquivDerivations
#print axioms jordanDerivationEquivDerivations_zero
#print axioms jordanDerivationEquivDerivations_add
#print axioms jordanDerivationEquivDerivations_smul
#print axioms jordanDerivationEquivDerivations_bracket
#print axioms bilinearAlgDerivationLieLane
#print axioms bilinearAlg_onsager_reciprocity

-- F8.2 Peirce Z2 / Superderivations
#print axioms squareZeroRingDifferentialToDerivations
#print axioms squareZeroRingDifferentialToDerivations_injective
#print axioms addLeibnizEquivIntDerivations
#print axioms superAnticomm_isLeibniz
#print axioms superAnticommToDerivations_oddDiff_eq
#print axioms superAnticommToDerivations_differentialPlus_differentialMinus_eq
#print axioms oddSuperderivation_even_bimodule_leibniz
#print axioms superAnticommEvenRestrict
#print axioms superAnticommLinearToDerivations
#print axioms superAnticommLinearEvenRestrict
#print axioms differentialJLinear
#print axioms differentialJLinear_isOdd
#print axioms peirceEvenSubalgebra_onsager_reciprocity

-- F8.3 Braided Derivations
#print axioms bicharacter_zero_left
#print axioms bicharacter_zero_right
#print axioms isTrivialBraidingDeg_zero
#print axioms braidedDerivation_isLeibniz_of_span
#print axioms braidedDerivation_isLeibniz_of_deg_zero_of_span
#print axioms braidedDerivation_isLeibniz_of_subring_closure_eq_top
#print axioms braidedDerivation_isLeibniz_of_algebra_adjoin_eq_top
#print axioms braidedDerivationRestrictSubring
#print axioms braidedDerivationRestrictSubalgebra
#print axioms braidedAlgebra_onsager_reciprocity
#print axioms braidedSubalgebra_onsager_reciprocity

-- F8.3 Guarded GradedBraidedDerivation & ZMod 2 Peirce Odd Link
#print axioms braidedDerivationToGraded
#print axioms braidedDerivationToGraded_injective
#print axioms gradedBraidedDerivation_isLeibniz_of_span
#print axioms gradedBraidedDerivation_isLeibniz_of_trivialDeg_of_span
#print axioms gradedBraidedDerivation_isLeibniz_of_deg_zero_of_span
#print axioms subring_closure_le_gradedBraidedLeibnizSubring
#print axioms gradedBraidedDerivation_isLeibniz_of_subring_closure_eq_top
#print axioms algebra_adjoin_le_gradedBraidedLeibnizSubalgebra
#print axioms gradedBraidedDerivation_isLeibniz_of_algebra_adjoin_eq_top
#print axioms gradedBraidedDerivationToIntDerivations
#print axioms gradedBraidedDerivationToDerivations
#print axioms gradedBraidedDerivationRestrictSubring
#print axioms gradedBraidedDerivationRestrictSubalgebra
#print axioms gradedBraidedDerivationRestrictTrivialAdjoin
#print axioms gradedBraidedDerivationLieLane
#print axioms gradedBraidedAlgebraOnsagerSystem
#print axioms gradedBraidedAlgebra_onsager_reciprocity
#print axioms zmod2SignBicharacter
#print axioms peirceZMod2Grade
#print axioms oddTwistSuperderivationToGradedBraided
#print axioms oddTwistSuperderivationToGradedBraided_injective

end ExplicitPrintAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owner : Name := `InfoGeometry.Canonical.ExceptionalZornSuperBraidedDerivationBridge
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless moduleNames.contains owner do
    throwError "AUDIT_FAILURE: missing imported owner {owner}"
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some modName := moduleNames[moduleIdx.toNat]? | continue
    if modName != owner then continue
    if let .axiomInfo _ := info then
      throwError "AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "AUDIT_FAILURE: {name} depends on disallowed axiom {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    if let .thmInfo _ := info then theorems := theorems + 1
  if count == 0 then
    throwError "AUDIT_FAILURE: empty audited owner {owner}"
  logInfo m!"AUDIT_OWNER: {owner}: {count} declarations ({theorems} theorems)"
  logInfo m!"AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"AUDIT_SUCCESS: {owner} verified clean"
