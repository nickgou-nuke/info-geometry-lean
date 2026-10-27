/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import «InfoGeometry».«Algebra».«NonAssocDerivation»
import «InfoGeometry».«Algebra».«DerivationLieLane»
import «InfoGeometry».«Algebra».«DerivationLieLaneRepresentation»
import «InfoGeometry».«OperatorAlgebra».«DerivationDifferentialForms»
import «InfoGeometry».«OperatorAlgebra».«DerivationGeometryTransport»
import «InfoGeometry».«Canonical».«ZornSpinor»
import «InfoGeometry».«Algebra».«ZornVectorMatrix»
import «InfoGeometry».«Algebra».«Zorn».«CanonicalVectorMatrixBridge»
import «InfoGeometry».«Lie».«CanonicalZornDerivation»
import «InfoGeometry».«Lie».«CanonicalZornDerivationLane»
import «InfoGeometry».«Lie».«CanonicalZornRegularOperators»
import «InfoGeometry».«Lie».«CanonicalZornRegularDerivation»
import «InfoGeometry».«Lie».«CanonicalZornOperatorDerivationLane»
import «InfoGeometry».«OperatorAlgebra».«DerivationVectorCalculus»
import «InfoGeometry».«OperatorAlgebra».«CanonicalZornDerivationDifferentialForms»
import «InfoGeometry».«Canonical».«SplitOctonionAutomorphismCore»
import «InfoGeometry».«Algebra».«AlternativeDerivations»
import «InfoGeometry».«Algebra».«ZornDerivationBridge»
import «InfoGeometry».«Algebra».«Zorn».«SplitOctonionDerivationConjugation»
import «InfoGeometry».«OperatorAlgebra».«CanonicalZornAutomorphismDifferentialForms»
import «InfoGeometry».«LinearAlgebra».«TraceAnticommutation»
import «InfoGeometry».«OperatorAlgebra».«IntrinsicGradedAdjoint»
import «InfoGeometry».«Algebra».«ZornLeftGrading»
import «InfoGeometry».«Algebra».«ZornLeftParity»
import «InfoGeometry».«Algebra».«ZornLeftMajorana»
import «InfoGeometry».«Algebra».«ChiralZornCARAndSchurBridge»
import «InfoGeometry».«Algebra».«ChiralCARTransport»
import «InfoGeometry».«Algebra».«ZornLeftMajoranaCovariance»
import «InfoGeometry».«OperatorAlgebra».«ZornMajoranaGradedCurvature»
import «InfoGeometry».«OperatorAlgebra».«ZornMajoranaSupertrace»
import «InfoGeometry».«Geometry».«AssociativeGaugeConnection»
import «InfoGeometry».«OperatorAlgebra».«DerivationGaugeTransport»
import «InfoGeometry».«OperatorAlgebra».«DerivationGaugeNaturality»
import «InfoGeometry».«Canonical».«OperatorBerezinianCore»
import «InfoGeometry».«OperatorAlgebra».«DerivationRightLogarithmicForm»
import «InfoGeometry».«Canonical».«OperatorBerezinianDifferential»
import «InfoGeometry».«Physics».«PoincarePauliLubanskiCovarianceBridge»
import «InfoGeometry».«Algebra».«Zorn».«OffDiagonalDerivation»
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `«InfoGeometry».«Algebra».«NonAssocDerivation»,
    `«InfoGeometry».«Algebra».«DerivationLieLane»,
    `«InfoGeometry».«Algebra».«DerivationLieLaneRepresentation»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationDifferentialForms»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationGeometryTransport»,
    `«InfoGeometry».«Canonical».«ZornSpinor»,
    `«InfoGeometry».«Algebra».«ZornVectorMatrix»,
    `«InfoGeometry».«Algebra».«Zorn».«CanonicalVectorMatrixBridge»,
    `«InfoGeometry».«Lie».«CanonicalZornDerivation»,
    `«InfoGeometry».«Lie».«CanonicalZornDerivationLane»,
    `«InfoGeometry».«Lie».«CanonicalZornRegularOperators»,
    `«InfoGeometry».«Lie».«CanonicalZornRegularDerivation»,
    `«InfoGeometry».«Lie».«CanonicalZornOperatorDerivationLane»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationVectorCalculus»,
    `«InfoGeometry».«OperatorAlgebra».«CanonicalZornDerivationDifferentialForms»,
    `«InfoGeometry».«Canonical».«SplitOctonionAutomorphismCore»,
    `«InfoGeometry».«Algebra».«AlternativeDerivations»,
    `«InfoGeometry».«Algebra».«ZornDerivationBridge»,
    `«InfoGeometry».«Algebra».«Zorn».«SplitOctonionDerivationConjugation»,
    `«InfoGeometry».«OperatorAlgebra».«CanonicalZornAutomorphismDifferentialForms»,
    `«InfoGeometry».«LinearAlgebra».«TraceAnticommutation»,
    `«InfoGeometry».«OperatorAlgebra».«IntrinsicGradedAdjoint»,
    `«InfoGeometry».«Algebra».«ZornLeftGrading»,
    `«InfoGeometry».«Algebra».«ZornLeftParity»,
    `«InfoGeometry».«Algebra».«ZornLeftMajorana»,
    `«InfoGeometry».«Algebra».«ChiralZornCARAndSchurBridge»,
    `«InfoGeometry».«Algebra».«ChiralCARTransport»,
    `«InfoGeometry».«Algebra».«ZornLeftMajoranaCovariance»,
    `«InfoGeometry».«OperatorAlgebra».«ZornMajoranaGradedCurvature»,
    `«InfoGeometry».«OperatorAlgebra».«ZornMajoranaSupertrace»,
    `«InfoGeometry».«Geometry».«AssociativeGaugeConnection»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationGaugeTransport»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationGaugeNaturality»,
    `«InfoGeometry».«Canonical».«OperatorBerezinianCore»,
    `«InfoGeometry».«OperatorAlgebra».«DerivationRightLogarithmicForm»,
    `«InfoGeometry».«Canonical».«OperatorBerezinianDifferential»,
    `«InfoGeometry».«Physics».«PoincarePauliLubanskiCovarianceBridge»,
    `«InfoGeometry».«Algebra».«Zorn».«OffDiagonalDerivation»]
  let commandOnly : Array Name := #[]
  for target in targets do
    unless env.header.moduleNames.contains target do
      throwError "Selected module not imported: {target}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut ownerCounts : NameMap Nat := {}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {name}"
    -- Public API handles imported axiom metadata and private-body lookup.
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
      if !allAxioms.contains ax then
        allAxioms := allAxioms.push ax
    count := count + 1
    ownerCounts := ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)
    logInfo m!"AUDIT_DECL: {owner}: {name}"
  for target in targets do
    let moduleCount := (ownerCounts.find? target).getD 0
    logInfo m!"AUDIT_MODULE_COUNT: {target}: {moduleCount}"
    if commandOnly.contains target then
      if moduleCount != 0 then
        throwError "Command-only module owns declarations: {target}"
      logInfo m!"AUDIT_COMMAND_MODULE: {target}"
    else
      if moduleCount == 0 then
        throwError "No declarations audited in reviewed module: {target}"
      logInfo m!"AUDIT_MODULE: {target}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_AXIOMS: {allAxioms.qsort Name.lt}"
  logInfo m!"AUDIT_COUNT: {count}"
