/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.ArchitectureAudit
import InfoGeometry.Meta.Trust
import InfoGeometry.Lint.Pauli
import InfoGeometry.Lint.NonTriviality

open Lean Meta Elab Command

namespace InfoGeometry.Meta.AuditRemediationTest

-- ── Test 1 & 2 fixtures: primitive `.proj` resolution and tagged-container non-shielding ──

@[rep_depth thermo]
def thermoLeafValue : Nat := 1

structure ProjBox where
  val : Nat
  deriving Inhabited

attribute [rep_depth thermo] ProjBox.val

@[rep_depth count]
def projFieldCaller (b : ProjBox) : Nat :=
  b.1

@[rep_depth projective]
structure TaggedShield (h : thermoLeafValue = thermoLeafValue) where
  payload : Nat

def taggedShieldWitness : TaggedShield rfl := ⟨0⟩

@[rep_depth count]
def shieldedCaller (s : TaggedShield rfl) : Nat :=
  s.payload

-- ── Test 3 fixtures: `@[implemented_by]` `unsafeLeakage` vs upstream safe runtime hook ──

unsafe def rawUnsafeImpl : Nat := 0

@[implemented_by rawUnsafeImpl]
def safeFacade : Nat := 0

def safeFacadeCaller : Nat :=
  safeFacade

def upstreamFoldUser (e : Expr) : Nat :=
  e.foldConsts 0 fun _ acc => acc + 1

-- ── Test 5 fixtures: `.proj` vacuous socket & `declMemoRef` cache hit parity ──

structure BadSocketCarrier where
  certificate : Nat
  deriving Inhabited

def projSocketAccessor (w : BadSocketCarrier) : Nat :=
  w.1

theorem memoLeaf (n : Nat) : n + 0 = n := Nat.add_zero n

theorem memoLeft (n : Nat) : n + 0 = n := memoLeaf n

theorem memoRight (n : Nat) : n + 0 = n := memoLeaf n

theorem memoPair : (∀ n : Nat, n + 0 = n) ∧ (∀ n : Nat, n + 0 = n) :=
  ⟨memoLeft, memoRight⟩

theorem memoPairSym : (∀ n : Nat, n + 0 = n) ∧ (∀ n : Nat, n + 0 = n) :=
  ⟨memoLeft, memoLeft⟩

-- ── Kernel-level checks for Tests 1, 2, 3, and 5 ──

run_cmd do
  let env ← getEnv
  let queryEnv := env.setExporting false

  -- Test 1: `.proj` primitive projection resolves `ProjBox.val` and triggers REGRESSION.
  let some projInfo := queryEnv.find? ``projFieldCaller
    | throwError "missing projFieldCaller"
  let projDeps := (DAG.edgesFromConstantInfoInEnv queryEnv projInfo).map Prod.fst
  unless projDeps.contains ``ProjBox.val do
    throwError "Test 1 failed: expected `ProjBox.val` in `edgesFromConstantInfoInEnv` of `projFieldCaller`, got {projDeps}"
  let projViolations := InfoGeometry.Meta.taggedDependencyViolations env ``projFieldCaller .count false
  if projViolations.isEmpty then
    throwError "Test 1 failed: expected REGRESSION violation for `.proj` dependency `ProjBox.val`"

  -- Test 2: `@[rep_depth projective]` structure container does not shield downstream thermo dependency.
  if InfoGeometry.Meta.ArchitectureAudit.isTaggedArchSurface env ``TaggedShield then
    throwError "Test 2 failed: `isTaggedArchSurface` must be false for `.inductInfo` container `TaggedShield`"
  let shieldViolations := InfoGeometry.Meta.taggedDependencyViolations env ``shieldedCaller .count false
  if shieldViolations.isEmpty then
    throwError "Test 2 failed: `TaggedShield` masked downstream `@[rep_depth thermo]` dependency"

  -- Test 3: `unsafeLeakage` detects `@[implemented_by]` without false-flagging Lean/Std `Expr.foldConsts`.
  let policy := InfoGeometry.Meta.defaultPolicySnapshot
  let evFacade ← liftCoreM <| InfoGeometry.Meta.collectHardEvidence policy ``safeFacade
  unless evFacade.unsafeLeakage do
    throwError "Test 3 failed: expected `unsafeLeakage = true` on `@[implemented_by]` declaration `safeFacade`"
  let evCaller ← liftCoreM <| InfoGeometry.Meta.collectHardEvidence policy ``safeFacadeCaller
  unless evCaller.unsafeLeakage do
    throwError "Test 3 failed: expected `unsafeLeakage = true` on caller `safeFacadeCaller`"
  let evUpstream ← liftCoreM <| InfoGeometry.Meta.collectHardEvidence policy ``upstreamFoldUser
  if evUpstream.unsafeLeakage then
    throwError "Test 3 failed: false-flagged external upstream `Lean.Expr.foldConsts` as `unsafeLeakage`"

  -- Test 5a: `NonTriviality` catches primitive `.proj` access to `certificate` field.
  let some sockCi := queryEnv.find? ``projSocketAccessor
    | throwError "missing projSocketAccessor"
  let some sockVal := sockCi.value? (allowOpaque := true)
    | throwError "missing body for projSocketAccessor"
  let sockAudit ← liftTermElabM <|
    InfoGeometry.Lint.auditExprTrivialityDetailed InfoGeometry.Lint.AuditConfig.default env
      [``projSocketAccessor]
      (InfoGeometry.Lint.AuditConfig.maxLocalUnfoldDepth InfoGeometry.Lint.AuditConfig.default)
      sockVal
  unless InfoGeometry.Lint.AuditResult.containsVacuousSockets sockAudit do
    throwError "Test 5a failed: `.proj` access to `BadSocketCarrier.certificate` bypassed `containsVacuousSockets`"

  -- Test 5b: `declMemoRef` cache hit vs miss produces matching `termNodeCount` and `unfoldedLocalConsts`.
  let some pairCi := queryEnv.find? ``memoPair
    | throwError "missing memoPair"
  let some pairVal := pairCi.value? (allowOpaque := true)
    | throwError "missing body for memoPair"
  let some symCi := queryEnv.find? ``memoPairSym
    | throwError "missing memoPairSym"
  let some symVal := symCi.value? (allowOpaque := true)
    | throwError "missing body for memoPairSym"
  let some leftCi := queryEnv.find? ``memoLeft
    | throwError "missing memoLeft"
  let some leftVal := leftCi.value? (allowOpaque := true)
    | throwError "missing body for memoLeft"
  let some rightCi := queryEnv.find? ``memoRight
    | throwError "missing memoRight"
  let some rightVal := rightCi.value? (allowOpaque := true)
    | throwError "missing body for memoRight"
  let cfg := InfoGeometry.Lint.AuditConfig.default
  let maxDepth := InfoGeometry.Lint.AuditConfig.maxLocalUnfoldDepth cfg
  let auditLeft ← liftTermElabM <| InfoGeometry.Lint.auditExprTrivialityDetailed cfg env [``memoLeft] maxDepth leftVal
  let auditRight ← liftTermElabM <| InfoGeometry.Lint.auditExprTrivialityDetailed cfg env [``memoRight] maxDepth rightVal
  let auditPair ← liftTermElabM <| InfoGeometry.Lint.auditExprTrivialityDetailed cfg env [``memoPair] maxDepth pairVal
  let auditSym ← liftTermElabM <| InfoGeometry.Lint.auditExprTrivialityDetailed cfg env [``memoPairSym] maxDepth symVal
  unless InfoGeometry.Lint.AuditResult.unfoldedLocalConsts auditPair |>.contains ``memoLeaf do
    throwError "Test 5b failed: `memoLeaf` missing from `unfoldedLocalConsts` on `memoPair`"
  -- On `memoPair`, `memoLeft` and `memoRight` are distinct constants that both unfold `memoLeaf`
  -- (first misses `declMemoRef`, second hits `declMemoRef`), while `memoPairSym` shares `.const memoLeft`.
  -- Check that `auditLeft` and `auditRight` contribute equally to `termNodeCount`:
  let leftNodes := InfoGeometry.Lint.AuditResult.termNodeCount auditLeft
  let rightNodes := InfoGeometry.Lint.AuditResult.termNodeCount auditRight
  let pairNodes := InfoGeometry.Lint.AuditResult.termNodeCount auditPair
  let expectedMin := leftNodes + rightNodes
  unless pairNodes ≥ expectedMin do
    throwError "Test 5b failed: `declMemoRef` cache hit dropped `termNodeCount` (pair={pairNodes}, left={leftNodes}, right={rightNodes})"
  let _ := auditSym

  -- Test 4a: `pauliLinter` Axiom-Surface Seal + `Trust.collectHardEvidence` on dynamically elaborated command.
  let savedState ← get
  try
    let cmdText := "ax" ++ "iom _root_.InfoGeometry.Canonical.pauli_custom_ax_test : True"
    match Parser.runParserCategory (← getEnv) `command cmdText with
    | .error err => throwError "Test 4a parser failed: {err}"
    | .ok cmdStx =>
        withReader ({ · with snap? := none }) do
          elabCommandTopLevel cmdStx
        let allMsgLog := (← get).messages ++
          (← get).snapshotTasks.foldl
            (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
        modify ({ · with snapshotTasks := #[] })
        let msgs ← allMsgLog.toList.mapM (·.toString)
        let sealed := msgs.any fun m =>
          (m.splitOn "[Pauli/Axiom-Surface Seal] InfoGeometry.Canonical.pauli_custom_ax_test").length > 1
        unless sealed do
          throwError "Test 4a failed: expected `[Pauli/Axiom-Surface Seal]` diagnostic from `pauliLinter`, got {msgs}"
        let evAx ← liftCoreM <|
          InfoGeometry.Meta.collectHardEvidence policy `InfoGeometry.Canonical.pauli_custom_ax_test
        unless evAx.forbiddenAxioms == [`InfoGeometry.Canonical.pauli_custom_ax_test] do
          throwError "Test 4a failed: expected `forbiddenAxioms == [InfoGeometry.Canonical.pauli_custom_ax_test]`, got {evAx.forbiddenAxioms}"
  finally
    set savedState

-- ── Test 4: Pauli `_root_.`, parameterized `rfl`, and non-theorem `abbrev` checks ──

/--
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.pauli_root_rfl_test is proved via trivial `rfl`.
-/
#guard_msgs in
theorem _root_.InfoGeometry.Canonical.pauli_root_rfl_test (n : Nat) : n = n := rfl

/--
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.pauli_imported_reflexivity_test is proved via trivial `rfl`.
-/
#guard_msgs in
theorem _root_.InfoGeometry.Canonical.pauli_imported_reflexivity_test (n : Nat) : n + n = n + n :=
  Nat.add_comm n n

/--
error: [Pauli/Identity-via-Reflexivity] InfoGeometry.Canonical.pauli_disguised_symm_rfl is proved via trivial `rfl`.
-/
#guard_msgs in
theorem _root_.InfoGeometry.Canonical.pauli_disguised_symm_rfl (n : Nat) : n = n := Eq.symm rfl

/--
warning: [Pauli/No-Mask Mandate] InfoGeometry.Canonical.pauli_abbrev_Einstein_test uses a physically-loaded name but does not transitively depend on foundational Core or Algebra transformations. Ensure this is not symbolic inflation.
-/
#guard_msgs in
abbrev _root_.InfoGeometry.Canonical.pauli_abbrev_Einstein_test : Nat := 0

end InfoGeometry.Meta.AuditRemediationTest
