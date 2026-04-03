# Typed Lean Compiler Bridge Contract

This document specifies a strongly typed Lean 4 compiler bridge for autonomous theorem generation and proof search.

It is designed to reuse the repository's existing Lean server foundations:

- `lean/scripts/DAG/Exploration/SemanticBlockServer.lean`
- `lean/DAG/SemanticServerRpc.lean`
- `lean/DAG/ServerExport.lean`

## Problem

Current automation layers are strong at graph extraction, policy checks, and report generation, but theorem synthesis loops still depend on weakly typed text interactions in critical steps.

For autonomous proving, the control loop must speak in typed requests and typed responses all the way to the Lean kernel.

## Goal

Provide a typed request/response API over Lean server RPC so an agent can:

1. submit candidate declarations and local proof edits
2. receive typed elaboration outcomes and goal states
3. run tactic steps with structured feedback
4. classify errors deterministically
5. validate final declarations by kernel check

## Non-Goals

This bridge is not a replacement for:

- `lake build` and normal repository quality gates
- DAG/report pipelines under `tools/infra`
- architecture and vacuity policy checks already enforced in Lean and Python

## Architecture

Use the same model as the semantic block server:

1. Lean worker process started via watchdog mode
2. LSP transport for file/session lifecycle
3. custom RPC procedures registered with `registerBuiltinRpcProcedure`
4. typed payloads deriving `FromJson` and `ToJson`

## Canonical Names

Use an explicit namespace for compiler bridge RPC procedures:

- `IG.Compiler.openSession`
- `IG.Compiler.closeSession`
- `IG.Compiler.checkSnippet`
- `IG.Compiler.getGoals`
- `IG.Compiler.runTactic`
- `IG.Compiler.applyEdit`
- `IG.Compiler.validateDecl`
- `IG.Compiler.getEnvFingerprint`

## Type Contract

All payloads should be tagged and versioned.

```lean
structure BridgeVersion where
  schema : Nat
  protocol : String
deriving FromJson, ToJson

structure SessionId where
  value : String
deriving BEq, Hashable, FromJson, ToJson

structure EnvFingerprint where
  leanToolchain : String
  importRoot : String
  nsFilter : String
  oleanHash : String
  artifactSchema : Nat
deriving FromJson, ToJson

inductive Severity where
  | info
  | warning
  | error
deriving FromJson, ToJson

inductive CompilerErrorCode where
  | parseError
  | elaborationError
  | unsolvedGoals
  | typeclassSearchFailed
  | unknownConstant
  | tacticFailed
  | timeout
  | internal
deriving FromJson, ToJson

structure CompilerError where
  code : CompilerErrorCode
  severity : Severity
  message : String
  file : String
  line : Nat
  column : Nat
deriving FromJson, ToJson

structure GoalView where
  goalId : String
  pretty : String
  hyps : Array String
  target : String
deriving FromJson, ToJson
```

## Request and Response Types

```lean
structure OpenSessionParams where
  version : BridgeVersion
  fileUri : String
  importRoot : String
  namespaceHint : String := "InfoGeometry"
  content : String
deriving FromJson, ToJson

structure OpenSessionResult where
  sessionId : SessionId
  env : EnvFingerprint
  diagnostics : Array CompilerError := #[]
deriving FromJson, ToJson

structure CheckSnippetParams where
  sessionId : SessionId
  content : String
  cursorLine : Nat := 0
  cursorCharacter : Nat := 0
deriving FromJson, ToJson

structure CheckSnippetResult where
  ok : Bool
  diagnostics : Array CompilerError
  goals : Array GoalView
deriving FromJson, ToJson

structure RunTacticParams where
  sessionId : SessionId
  goalId : String
  tactic : String
deriving FromJson, ToJson

structure RunTacticResult where
  ok : Bool
  diagnostics : Array CompilerError
  goalsAfter : Array GoalView
  closedGoals : Array String
deriving FromJson, ToJson

structure ValidateDeclParams where
  sessionId : SessionId
  declName : String
deriving FromJson, ToJson

structure ValidateDeclResult where
  ok : Bool
  diagnostics : Array CompilerError
  theoremType : String := ""
  hasSorry : Bool := false
deriving FromJson, ToJson
```

## Error Algebra Requirements

The bridge must never return raw error strings only.

Each error includes:

1. stable error code
2. source position
3. human-readable message
4. severity
5. phase origin (parse, elaboration, tactic, validation)

This allows autonomous search to branch on machine-checkable signals.

## Determinism and Reproducibility

Every session response should include or reference an environment fingerprint:

1. `lean-toolchain`
2. `importRoot`
3. namespace filter
4. `artifacts/dag/index/meta.json` `schemaVersion`
5. `artifacts/dag/index/meta.json` `oleanHash`

Any mismatch means the agent should discard cached proof attempts.

## Minimal Shipping Surface (Phase 1)

Implement this first, no more:

1. `openSession`
2. `checkSnippet`
3. `getGoals`
4. `runTactic`
5. `validateDecl`
6. `closeSession`

Keep all results typed and side-effect free outside the current session file.

## Recommended Lean File Layout

Add new server files analogous to semantic server setup:

1. `lean/DAG/CompilerBridgeTypes.lean`
2. `lean/DAG/CompilerBridgeRpc.lean`
3. `lean/scripts/DAG/Exploration/CompilerBridgeServer.lean`

And a Python client helper:

1. `tools/frontier/compiler_bridge_client.py`

## Existing Infra Reuse

Use current patterns directly:

1. `@[server_rpc_method]` request handlers as in `ServerExport.lean`
2. `registerBuiltinRpcProcedure` registration pattern
3. LSP transport lifecycle already implemented in `semantic_block_export.py`

Do not invent a second process model.

## Validation Gates

A generated theorem is accepted only if all are true:

1. `validateDecl.ok = true`
2. `hasSorry = false`
3. no error diagnostics
4. repository checks still pass (`strictCheck`, vacuity policy, architecture audit)

## Example Agent Loop

1. open session with candidate file content
2. check snippet and read typed goals
3. run one tactic step
4. if failed, branch on `CompilerErrorCode`
5. iterate until goals close
6. validate declaration
7. run repository gates

## Migration Plan

Phase A:

1. add bridge type definitions
2. expose `openSession`, `checkSnippet`, `getGoals`
3. wire Python client with typed decode

Phase B:

1. expose `runTactic` and `applyEdit`
2. add deterministic error code mapping
3. add environment fingerprint in every response

Phase C:

1. expose `validateDecl`
2. integrate with vacuity and architecture gates
3. integrate with autonomous theorem generation driver

## Acceptance Criteria

The bridge is complete when:

1. no autonomous proving path depends on regex over raw Lean output
2. all compile and tactic outcomes are represented by typed result values
3. replaying the same request sequence under the same fingerprint yields equivalent outcomes
4. final theorem acceptance is kernel checked and policy gated
