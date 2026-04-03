# Typed Lean Compiler Service

## Thesis

For autonomous theorem generation, the missing component is not a new theorem prover
beside Lean. It is a typed compiler-facing service over Lean's existing kernel,
elaborator, and server snapshots.

Lean already has the strong typing.
What the agent stack lacks is reliable typed access to:
- proof states
- local context
- metavariables
- elaboration failures
- declaration attributes
- semantic diffs between checkpoints

Without that layer, automation becomes stringly:
- scrape pretty-printed goals
- retry tactics from text diagnostics
- lose semantic identity across refactors
- fail to preserve metadata like role tags or ownership

The recent vacuity-tag plumbing problem in this repo is a small version of the same
issue: semantic state existed inside Lean, but the external pipeline could not see it.

## Existing Substrate In This Repo

This repository already contains the beginnings of the right architecture.

Lean-side export and RPC:
- [lean/DAG/SemanticServerRpc.lean](../lean/DAG/SemanticServerRpc.lean)
- [lean/DAG/ServerExport.lean](../lean/DAG/ServerExport.lean)
- [lean/DAG/BlockExport.lean](../lean/DAG/BlockExport.lean)

Kernel-grounded export:
- [lean/DAG/Indexer.lean](../lean/DAG/Indexer.lean)
- [lean/DAG/ProcessFlowExport.lean](../lean/DAG/ProcessFlowExport.lean)
- [lean/DAG/RepresentationDepthExport.lean](../lean/DAG/RepresentationDepthExport.lean)

Native semantic grammar:
- [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
- [lean/InfoGeometry/Meta/Vacuity.lean](../lean/InfoGeometry/Meta/Vacuity.lean)

Current infra consumers:
- [tools/infra/README.md](../tools/infra/README.md)
- [docs/OperationalIntent.md](OperationalIntent.md)

The gap is that these surfaces are mostly declaration-graph oriented, file oriented,
or block oriented. They are not yet a typed proof-state compiler service.

## What Is Missing

The missing interface is a session- and proof-oriented semantic API with:

1. Stable goal identity
2. Typed local context export
3. Structured expression export
4. Incremental elaboration checkpoints
5. Machine-readable error causes
6. Replayable proof actions with semantic diff output

Today, an autonomous agent can ask:
- "What declarations depend on this theorem?"
- "What blocks produce these names?"

But it cannot cleanly ask:
- "What is the current metavariable forest for this theorem body?"
- "Which local hypotheses were introduced since the last action?"
- "Did elaboration fail from coercion search, typeclass synthesis, or unification?"
- "Which proof obligations remain after this candidate term?"
- "What declaration metadata changed semantically, not textually?"

## Proposed Architecture

### 1. Typed Semantic IR

Add a Lean-native protocol layer that exports proof-relevant structures as stable JSON.

Suggested module family:
- `lean/Agent/Protocol.lean`
- `lean/Agent/ExprCodec.lean`
- `lean/Agent/ProofStateExport.lean`
- `lean/Agent/ElabTraceExport.lean`
- `lean/Agent/ProofServerRpc.lean`

Core principle:
- keep the kernel as source of truth
- export typed summaries, not raw pretty-printed strings

Minimal protocol types:

```lean
structure GoalId where
  id : String
deriving ToJson, FromJson

structure LocalDeclView where
  userName : String
  fvarId : String
  binderInfo : String
  typeExpr : Json
  valueExpr? : Option Json
  isAuxDecl : Bool
deriving ToJson, FromJson

structure GoalView where
  goalId : GoalId
  targetExpr : Json
  localDecls : Array LocalDeclView
  tag : String
deriving ToJson, FromJson

structure ProofStateView where
  theoremName : Name
  snapshotId : String
  goals : Array GoalView
  solvedGoals : Array GoalId
  introducedDecls : Array Name
deriving ToJson, FromJson
```

The `Json` placeholders above should eventually become a typed expression codec with
constructors for:
- constants
- applications
- foralls
- lambdas
- lets
- projections
- literals
- metavariables
- free variables

Two views should be exported:
- lossless kernel view for replay
- summarized agent view for ranking and prompting

### 2. Compiler Session Service

Build a session-oriented RPC layer on top of Lean snapshots.

This should not be file-export only. It should manage:
- open document URI
- snapshot identity
- theorem target
- current proof body region
- local semantic state

Suggested RPC endpoints:
- `agent.openTheorem`
- `agent.getProofState`
- `agent.applyTermCandidate`
- `agent.applyTacticCandidate`
- `agent.refineHole`
- `agent.rollback`
- `agent.commitIfClosed`
- `agent.explainError`

Required response contract:
- next proof state
- semantic diff against previous state
- typed error report when applicable
- affected declarations if elaboration changed more than the target theorem

### 3. Typed Elaboration Errors

Autonomous proving needs structured failure modes.

Instead of only returning pretty strings, return classified errors such as:
- unknown constant
- type mismatch
- failed typeclass synthesis
- unsolved goals
- universe constraint failure
- invalid recursion
- termination failure
- tactic timeout
- reducibility mismatch

Example schema:

```lean
inductive ElabErrorKind where
  | unknownConstant
  | typeMismatch
  | instanceSynthesisFailure
  | unsolvedGoals
  | universeMismatch
  | tacticFailure
  | timeout
  | other
deriving ToJson, FromJson
```

This matters because agent policy should branch on error class, not regex over text.

### 4. Incremental Semantic Diffs

Every proof action should produce a semantic diff:
- goals removed
- goals introduced
- local hypotheses introduced
- local hypotheses cleared
- term accepted but generated side obligations
- declaration body changed but statement preserved

That gives the agent a stable optimization target:
- reduce open goal count
- reduce hard goals first
- preserve statement identity
- avoid hidden regressions

This is the proof analogue of the repo's declaration-graph refresh pipeline.

### 5. Theorem Synthesis Contract

The generator loop should produce typed drafts, not raw text blobs.

Suggested stages:

1. `TheoremRequest`
2. `DraftSignature`
3. `ObligationForest`
4. `ProofAttempt`
5. `CheckedDeclaration`

Example:

```lean
structure TheoremRequest where
  namespaceHint : Name
  dependencies : Array Name
  informalIntent : String

structure DraftSignature where
  proposedName : Name
  typeExpr : Json
  requiresNewDefs : Bool

structure ProofAttempt where
  proofTerm : Json
  consumedGoals : Array GoalId
  remainingGoals : Array GoalId
```

This lets the system reject or refine drafts before they become text edits.

### 6. Repo Integration

The current DAG stack should not be replaced. It should become the outer memory layer.

Recommended division:

- Lean compiler service
  - local proof state
  - elaboration
  - theorem synthesis
  - semantic diffs

- DAG and infra layer
  - global ownership
  - structural pressure
  - theorem-surface burden
  - dependency corridor guidance

In other words:
- compiler service chooses the next proof action
- DAG service chooses the next theorem or file to work on

## Concrete Implementation Path

### Phase 0

Stabilize semantic metadata export.

Already partly present in this repo:
- rep-depth tags
- capstone tags
- vacuity-role tags

Rule:
- every semantic attribute that matters to automation must survive into `decls.jsonl`

### Phase 1

Extend the existing server export into a typed declaration-and-block semantic service.

Start from:
- [lean/DAG/SemanticServerRpc.lean](../lean/DAG/SemanticServerRpc.lean)
- [lean/DAG/ServerExport.lean](../lean/DAG/ServerExport.lean)

Add:
- theorem target lookup
- declaration statement export
- attribute export
- local block-to-declaration provenance

### Phase 2

Add proof-state export from snapshots.

Focus on:
- active goals
- target expressions
- local hypotheses
- metavariable IDs
- theorem body region tracking

This is the first version useful for autonomous proving.

### Phase 3

Add action RPCs with rollback.

Required operations:
- apply term
- apply tactic
- synthesize exact
- revert to prior snapshot
- commit only when theorem closes

This creates a real proof compiler loop rather than a text-edit loop.

### Phase 4

Add typed elaboration traces and learning artifacts.

Export:
- successful action histories
- failed action classes
- goal-shape fingerprints
- theorem completion traces

These become training data for synthesis and repair policies.

## Design Constraints

The service must preserve these invariants:

1. Kernel-first
   - no external proof state may count as truth unless replayed by Lean

2. Statement safety
   - theorem headers may not drift without explicit approval

3. Incrementality
   - actions should reuse snapshots, not rebuild the whole environment

4. Stable identity
   - goals, declarations, and local hypotheses need machine identities

5. Lossless fallback
   - if summary codecs fail, the system must still keep a lossless kernel-facing form

## Non-Goals

This service is not:
- a replacement for Lean's kernel
- an excuse to bypass elaboration
- a free-form LLM patch loop over `.lean` text
- a Python-defined proof engine

Python should orchestrate.
Lean should decide.

## Why This Matters For This Repo

This repository is unusually well positioned to build such a system because it already has:
- a typed semantic ladder
- native architecture audits
- declaration export
- process-flow export
- server-side semantic block RPC
- downstream infra that can rank pressure and choose the next target

So the missing piece is not theory, and not even basic export.
It is the proof-state compiler service sitting between:
- local elaboration
- global structural memory
- autonomous theorem generation

## Suggested Next Build Target

If this proposal is implemented, the first concrete milestone should be:

`agent.getProofState`

for a single theorem in an open file, returning:
- theorem name
- snapshot ID
- goals
- typed local context
- attributes and semantic tags on the target declaration

Once that exists, autonomous proving becomes an engineering problem instead of a text-parsing problem.
