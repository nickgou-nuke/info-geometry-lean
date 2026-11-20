/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections
import InfoGeometry.Geometry.DivergenceMixedHessianCounterexample
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Declaration audit for statistical geometry boundaries

Inspect every declaration in the three new mathematical owners and their reused
dual-connection owner, including private and generated constants.
This follows the maintained `CliffordPeirceWalshAudit` command pattern. The
source/semantic review and the freshness of imported artifacts are separate
checks, documented in `docs/STATISTICAL_GEOMETRY_BOUNDARIES_CONTRACT.md`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample,
    `InfoGeometry.Modular.AmariChentsovDualConnections]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let required : Array Name := #[
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity.pureTrace_symmetry_smul_eq,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity.pureTrace_symmetry_span_eq_top,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity.pureTrace_symmetry_finrank_le_one,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity.pureTrace_symmetric_iff_oneForm_eq_zero,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity.one_dimensional_nonzero_example,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections.metricBilinForm_nondegenerate,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections.cubic_pureTrace_oneForm_eq_zero,
    `InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections.cubic_pureTrace_connections_eq,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.divergence_eq_zero_iff,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.contDiff_divergence,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.hasDerivAt_deriv_divergence_right,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.mixedHessian_diagonal_pos,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.mixedHessian_one_zero,
    `InfoGeometry.Geometry.DivergenceMixedHessianCounterexample.not_forall_mixedHessian_ne_zero]
  for name in required do
    unless env.contains name do
      throwError "AUDIT_FAILURE: missing required declaration {name}"
  logInfo m!"AUDIT_REQUIRED_DECLARATIONS: {required.size}"
  for owner in owners do
    unless moduleNames.contains owner do
      throwError "AUDIT_FAILURE: missing imported owner {owner}"
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  let mut counts : NameMap Nat := {}
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let some owner := moduleNames[moduleIdx.toNat]? | continue
    if !owners.contains owner then continue
    if let .axiomInfo _ := info then
      throwError "AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "AUDIT_FAILURE: {name} depends on {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
    if let .thmInfo _ := info then theorems := theorems + 1
  for owner in owners do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "AUDIT_FAILURE: empty audited owner {owner}"
    logInfo m!"AUDIT_OWNER: {owner}: {n}"
  logInfo m!"AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"AUDIT_DECLARATIONS: {count}"
  logInfo m!"AUDIT_THEOREMS_INCLUDING_GENERATED: {theorems}"
  logInfo m!"AUDIT_SUCCESS: {owners.size} owners"
