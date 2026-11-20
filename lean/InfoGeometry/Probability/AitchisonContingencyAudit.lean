/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.AitchisonContingencyDimensions
import InfoGeometry.Probability.AitchisonContingencyProbability
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Declaration audit for the finite contingency-table projection

Inspect every declaration in the three new mathematical owners and their three
directly reused repository owners, including private and generated constants.
This follows the maintained `CliffordPeirceWalshAudit` command pattern. The
source/semantic review and the freshness of imported artifacts are separate
checks, documented in `docs/AITCHISON_CONTINGENCY_CONTRACT.md`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Probability.AitchisonContingency,
    `InfoGeometry.Probability.AitchisonContingencyDimensions,
    `InfoGeometry.Probability.AitchisonContingencyProbability,
    `InfoGeometry.Probability.BipartiteLogCoupling,
    `InfoGeometry.Convex.LogSumExp,
    `InfoGeometry.Algebra.FiniteSpinAlgebra]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let required : Array Name := #[
    `InfoGeometry.Probability.AitchisonContingency.interaction_idempotent,
    `InfoGeometry.Probability.AitchisonContingency.interaction_self_adjoint,
    `InfoGeometry.Probability.AitchisonContingency.mem_additiveSubspace_iff,
    `InfoGeometry.Probability.AitchisonContingency.mem_interactionSubspace_iff,
    `InfoGeometry.Probability.AitchisonContingency.additive_pythagorean,
    `InfoGeometry.Probability.AitchisonContingency.additive_best_approximation_eq_iff,
    `InfoGeometry.Probability.AitchisonContingency.softmaxSimplex_clr,
    `InfoGeometry.Probability.AitchisonContingency.clr_injective,
    `InfoGeometry.Probability.AitchisonContingency.clr_independentProjection,
    `InfoGeometry.Probability.AitchisonContingency.independent_interaction_reconstruction,
    `InfoGeometry.Probability.AitchisonContingency.independent_pythagorean,
    `InfoGeometry.Probability.AitchisonContingency.independent_best_approximation,
    `InfoGeometry.Probability.AitchisonContingency.independent_best_approximation_eq_iff,
    `InfoGeometry.Probability.AitchisonContingency.projection_residual_sq,
    `InfoGeometry.Probability.AitchisonContingency.finrank_interactionSubspace,
    `InfoGeometry.Probability.AitchisonContingency.finrank_additiveSubspace,
    `InfoGeometry.Probability.AitchisonContingency.finrank_centeredAdditiveSubspace,
    `InfoGeometry.Probability.AitchisonContingency.finrank_centeredSubspace]
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
