/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityModular
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Exact-owner trust audit for the Plücker/infinity/modular addition

The substantive new and repaired modules are selected by imported-module ownership,
not declaration-name prefixes. Every owned constant, including private and
compiler-generated declarations present in the imported environment, is
checked for forbidden declaration kinds and transitive axiom dependencies.
The aggregate module is import-only and must own no declarations.

Counts below are kernel declaration counts. In particular theorem counts
include generated theorem declarations and need not match source keywords.
This audit establishes the trust boundary, not mathematical semantics.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Canonical.Cl55ChiralAnalyticKMS,
    `InfoGeometry.Canonical.Cl55InfinityChiralCharge,
    `InfoGeometry.Canonical.Cl55InfinityGradeReversal,
    `InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading,
    `InfoGeometry.Canonical.Cl55WittInternalFiveGrading,
    `InfoGeometry.Canonical.ComplexOperatorBilingualAnalyticity,
    `InfoGeometry.Canonical.ExteriorContractionOperatorBridge,
    `InfoGeometry.Canonical.ExteriorFockOperatorLaws,
    `InfoGeometry.Canonical.FilteredGNSHestenesPhaseCone,
    `InfoGeometry.Canonical.FilteredGNSMatrixAnalyticKMS,
    `InfoGeometry.Canonical.FiniteFaithfulGNSTomitaClosability,
    `InfoGeometry.Canonical.FiniteMatrixGibbsFaithfulness,
    `InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability,
    `InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS,
    `InfoGeometry.Canonical.FockNumberOperatorBridge,
    `InfoGeometry.Canonical.FockVacuumAnnihilationBridge,
    `InfoGeometry.Canonical.FullCARAnticommutationAlgebraBridge,
    `InfoGeometry.Canonical.MatrixTraceTomitaColimit,
    `InfoGeometry.Canonical.RealModularConjugationBridge,
    `InfoGeometry.Canonical.TracialGNSTomitaClosability,
    `InfoGeometry.Canonical.VacuumExpectationCARBridge,
    `InfoGeometry.Clifford.Cl55NativeInternalFiveGrading,
    `InfoGeometry.Clifford.Cl55WittCalibratedColimit,
    `InfoGeometry.Clifford.Cl55WittCalibratedGamma,
    `InfoGeometry.Clifford.Cl55WittCalibratedHermitian,
    `InfoGeometry.Clifford.Cl55WittCalibratedRepresentation,
    `InfoGeometry.OperatorAlgebra.ComplexTimeCorrelation,
    `InfoGeometry.Projective.ExteriorKleinCliffordInversion,
    `InfoGeometry.Twistor.InfinityTwistor,
    `InfoGeometry.Twistor.PluckerBlockInversion,
    `InfoGeometry.Twistor.PluckerCl55InfinityBridge,
    `InfoGeometry.Twistor.PluckerInfinityChart,
    `InfoGeometry.Twistor.PluckerInfinityGeometry,
    `InfoGeometry.Twistor.PluckerLorentzRealForm,
    `InfoGeometry.Twistor.PluckerPenroseIncidence,
    `InfoGeometry.Twistor.PluckerPinAffineRestriction,
    `InfoGeometry.Twistor.PluckerPinEndpointStabilizers,
    `InfoGeometry.Twistor.PluckerSheetReflection,
    `InfoGeometry.Twistor.WittenCl55ExteriorBridge,
    `InfoGeometry.Twistor.WittenCollinearityOperator,
    `InfoGeometry.Twistor.WittenExteriorHelicity,
    `InfoGeometry.Twistor.WittenExteriorScalarExtension,
    `InfoGeometry.Twistor.WittenIncidence,
    `InfoGeometry.Twistor.WittenParkeTaylor,
    `InfoGeometry.Twistor.WittenSpinorBCFW,
    `InfoGeometry.Twistor.WittenSpinorHelicity]
  let aggregate : Name := `InfoGeometry.Twistor.PluckerInfinityModular
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless moduleNames.contains owner do
      throwError "AUDIT_FAILURE: selected owner is not imported: {owner}"
  unless moduleNames.contains aggregate do
    throwError "AUDIT_FAILURE: aggregate is not imported: {aggregate}"
  let mut declarationCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut ownerCounts : NameMap Nat := {}
  let mut ownerTheoremCounts : NameMap Nat := {}
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some owner := moduleNames[moduleIdx.toNat]? |
      throwError "AUDIT_FAILURE: invalid module index for declaration: {name}"
    if owner == aggregate then
      throwError "AUDIT_FAILURE: import-only aggregate owns a declaration: {name}"
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "AUDIT_FAILURE: owner introduces an axiom: {owner}: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "AUDIT_FAILURE: unsafe or partial declaration: {owner}: {name}"
    liftIO do
      let err ← IO.getStderr
      err.putStrLn s!"AUDIT_CHECK: {owner}: {name}"
      err.flush
    -- The public API follows imported axiom metadata and private dependencies.
    for axiomName in (← Lean.collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "AUDIT_FAILURE: disallowed transitive axiom: {axiomName}: {name}"
      if !allAxioms.contains axiomName then
        allAxioms := allAxioms.push axiomName
    declarationCount := declarationCount + 1
    ownerCounts := ownerCounts.insert owner ((ownerCounts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
      ownerTheoremCounts := ownerTheoremCounts.insert owner
        ((ownerTheoremCounts.find? owner).getD 0 + 1)
  for owner in owners do
    let count := (ownerCounts.find? owner).getD 0
    let theorems := (ownerTheoremCounts.find? owner).getD 0
    if count == 0 then
      throwError "AUDIT_FAILURE: selected owner has no audited declarations: {owner}"
    logInfo m!"AUDIT_MODULE_COUNT: {owner}: {count}"
    logInfo m!"AUDIT_MODULE_THEOREM_COUNT: {owner}: {theorems}"
  logInfo m!"AUDIT_AGGREGATE: {aggregate}: 0"
  logInfo m!"AUDIT_OWNER_COUNT: {owners.size}"
  logInfo m!"AUDIT_AXIOMS: {allAxioms.qsort Name.lt}"
  logInfo m!"AUDIT_COUNT: {declarationCount}"
  logInfo m!"AUDIT_THEOREM_COUNT: {theoremCount}"
  logInfo m!"AUDIT_SUCCESS: all {owners.size} owners passed the exact-owner trust audit"
