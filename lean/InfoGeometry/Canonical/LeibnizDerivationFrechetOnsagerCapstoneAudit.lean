/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom and Integrity Audit for `LeibnizDerivationFrechetOnsagerCapstone`

Verifies via both explicit `#print axioms` on every exported Capstone declaration
and an environment-wide `Lean.Util.CollectAxioms` sweep that all constants in
`InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone` depend strictly on
`{propext, Classical.choice, Quot.sound}`.
-/

section ExplicitPrintAxioms

open InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone

-- Core Spine Structures & Canonical Constructors
#print axioms UnifiedDerivationOnsagerFormSpine
#print axioms UnifiedDerivationOnsagerFormSpine.ofParitySystem
#print axioms canonicalUnifiedDerivationOnsagerFormSpine
#print axioms LeibnizDerivationFrechetOnsagerSpine
#print axioms canonicalStarCapstoneSpine
#print axioms canonicalAutCapstoneSpine
#print axioms capstoneQubitSpine

-- All 6 Cross-Gap Pair Integration Theorems (T3-AB, BC, AD, DB, CD, AC)
#print axioms gapAB_peirceCut_ceBKM_parity_bridge
#print axioms gapAB_cartanSplit_parityFormPairing_bridge
#print axioms gapBC_frechetHessian_gibbsTrajectory_secondLaw
#print axioms gapAD_peirceCut_superAnticomm_cartan_bridge
#print axioms gapAD_bridgedLane_cartanOnsager_bridge
#print axioms gapDB_modularDerivation_ceBKM_parityForm_bridge
#print axioms gapDB_superBraided_ceBKM_curvature_bridge
#print axioms gapCD_modularDerivation_metriplecticFlow_secondLaw
#print axioms gapCD_exceptionalSuperDerivation_metriplecticFlow_secondLaw
#print axioms gapAC_cartanSchur_metriplecticFlow_secondLaw
#print axioms gapAC_peirceCut_matrixKuboMori_secondLaw

-- Master 4-Pillar Synthesis & Noncommutative n = 2 Witness
#print axioms four_pillar_unified_capstone
#print axioms capstone_qubit_nondegenerate_witness

end ExplicitPrintAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owner : Name := `InfoGeometry.Canonical.LeibnizDerivationFrechetOnsagerCapstone
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
