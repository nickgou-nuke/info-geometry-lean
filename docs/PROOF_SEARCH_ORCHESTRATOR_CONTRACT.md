# Proof Search Orchestrator Contract

This document specifies the machine-level contract for the Info-Geometry OS
proof-search orchestrator.

It complements `INFO_GEOMETRY_OS_ARCHITECTURE.md` and the existing
`RAW_INFOTREE_EXPORT_CONTRACT.md`.

## 1. Authority model

Lean is the proof authority.

ArangoDB is graph memory and audit state.

The LLM is a candidate generator.

The Python orchestrator is responsible for retrieval, search, validation,
patching, and telemetry.

No graph hit, motif, embedding, process-flow signal, or LLM output is proof
evidence until Lean accepts it.

## 2. Required input artifacts

The orchestrator may consume these surfaces:

```text
.lean source files
.olean compiled module artifacts
.ilean reference/location sidecars
declaration/dependency JSONL exports
raw_infotree_* JSONL or Arango collections
SCC/dominator/motif/process-flow overlays
prior proof-attempt telemetry
negative cache
```

The orchestrator must preserve artifact provenance in every generated packet.

## 3. Target packet

Each proof target should be normalized into a packet with at least:

```json
{
  "targetDeclName": "InfoGeometry.Example.foo",
  "module": "InfoGeometry.Example",
  "file": "lean/InfoGeometry/Example.lean",
  "sourceRange": {"start": "...", "end": "..."},
  "targetType": "...",
  "proofState": "open|sorry|admit|failed",
  "environmentKey": "...",
  "importsHash": "...",
  "artifactProvenance": {
    "olean": "...",
    "ilean": "...",
    "dependencyExport": "...",
    "rawInfoTreeExport": "..."
  }
}
```

Unknown fields must be explicit `null` or absent with a leakage/unknown-state
reason.  They must not be silently coerced to empty strings, zero, or false.

## 4. Retrieval contract

The retriever should return a context packet, not raw unstructured text.

Minimum fields:

```json
{
  "targetDeclName": "...",
  "strictDominators": [],
  "ownerDeclarations": [],
  "nearestSCC": [],
  "motifs": [],
  "rewriteCandidates": [],
  "simpCandidates": [],
  "priorSolvedGoalShapes": [],
  "negativeCacheExclusions": [],
  "rawInfoTreePointers": [],
  "provenance": []
}
```

Every declaration snippet must include:

```json
{
  "declName": "...",
  "module": "...",
  "type": "...",
  "kind": "theorem|def|lemma|structure|instance|unknown",
  "sourceRange": "...",
  "provenance": "olean|ilean|decl_export|raw_infotree|manual"
}
```

Motifs are guidance only.  They must not become proof assumptions unless a
Lean-side context field or theorem states them explicitly.

## 5. Prompt schema

The prompt has a stable prefix and a variable suffix.

Stable prefix:

```text
system/tool instruction for Lean proof generation
target declaration
imports and namespace context
retrieved owner declarations
strict dominators
motif summaries
simp/rw/theorem hints
negative-cache exclusions
current goals and local context
```

Variable suffix:

```text
candidate tactic or proof fragment request
```

The model should receive concrete Lean syntax and goal text.  Structural hashes
and De Bruijn-invariant references are for retrieval and cache keys, not the
primary generative representation.

## 6. LSP evaluation contract

For each candidate, the orchestrator must record:

```json
{
  "attemptId": "...",
  "targetDeclName": "...",
  "nodeId": "...",
  "candidateText": "...",
  "candidateHash": "...",
  "preGoalShapeHash": "...",
  "postGoalShapeHashes": [],
  "diagnostics": [],
  "lspStatus": "accepted|rejected|timeout|crash",
  "unsolvedGoalCount": 0,
  "elapsedMs": 0
}
```

Lean LSP success is not final proof acceptance.  A closed candidate must pass a
focused build.

## 7. Build gate contract

Acceptance levels:

`LSP-progress`: candidate elaborates and changes goals.

`LSP-closed`: candidate leaves no interactive goals.

`focused-build-closed`: target module builds.

`corridor-build-closed`: affected import/check corridor builds.

`review-ready`: focused or corridor build passes and the patch is isolated on
an agent branch.

The orchestrator may only mark a proof as verified after at least
`focused-build-closed`.

## 8. Negative cache key

Negative cache entries must be context-sensitive.

Required key fields:

```json
{
  "targetDeclName": "...",
  "goalShapeHash": "...",
  "localContextHash": "...",
  "environmentKey": "...",
  "importsHash": "...",
  "tacticTextHash": "...",
  "diagnosticClass": "type_mismatch|unknown_identifier|timeout|kernel_error|other"
}
```

Optional fields:

```json
{
  "normalizedTacticHash": "...",
  "modelId": "...",
  "retrievalPacketHash": "...",
  "leanVersion": "...",
  "mathlibRevision": "..."
}
```

Do not globally ban a tactic text merely because it failed once.

## 9. Goal shape hashing

Goal shape hashing must normalize irrelevant names while preserving proof
semantics.

The hash should account for:

```text
target expression shape
universe parameters
local hypotheses up to alpha-equivalence
typeclass assumptions
available declarations/imports
```

The hash must not claim semantic equivalence beyond what the normalizer
actually proves or approximates.  Approximate hashes are retrieval hints, not
definitional equality.

## 10. Reward contract

Hard success:

```text
no unsolved goals
focused build passes
```

Strong positive reward:

```text
goal count decreases
AST/expression complexity decreases
post-goal shape matches known solved lemma
candidate creates useful local theorem/hypothesis
```

Weak positive reward:

```text
candidate elaborates
new goals are more directly retrievable
diagnostics disappear but goals remain
```

Negative reward:

```text
type mismatch
unknown identifier
timeout
goal explosion
same goal shape repeats
```

Reward rows must store the features that produced the reward, not just the
scalar.

## 11. Patch policy

The orchestrator must preserve unrelated user changes.

Patch flow:

```text
read target file
apply minimal proof patch
run LSP or lean check
run focused lake build
write telemetry
leave patch in working tree or commit to agent branch
```

The orchestrator must not:

```text
commit directly to main
rewrite unrelated files
delete user edits
use destructive git commands
mark graph-derived claims as theorems without Lean proof
```

## 12. Telemetry tables

Recommended logical collections or JSONL streams:

```text
proof_targets
retrieval_packets
prompt_packets
mcts_nodes
proof_attempts
lsp_diagnostics
build_results
negative_cache
goal_shape_cache
patch_events
verification_events
```

Each row should include:

```text
runId
attemptId
targetDeclName
timestamp
toolVersion
leanVersion
gitCommit or workingTreeFingerprint
provenance
```

## 13. AQL retrieval shapes

The orchestrator should support at least these retrieval families:

Strict dominator retrieval:

```aql
FOR d IN arango_dag_dominators
  FILTER d.target == @targetDeclName
  SORT d.depth ASC
  LIMIT @limit
  RETURN d
```

Motif retrieval:

```aql
FOR m IN arango_dag_motifs
  FILTER @targetComponent IN m.componentKeys
  FILTER m.motif IN ["CommutativeSquare", "Diamond", "Span", "Cospan"]
  LIMIT @limit
  RETURN m
```

Prior goal-shape retrieval:

```aql
FOR g IN goal_shape_cache
  FILTER g.shapeHash == @goalShapeHash
  SORT g.successScore DESC
  LIMIT @limit
  RETURN g
```

Negative cache retrieval:

```aql
FOR n IN negative_cache
  FILTER n.targetDeclName == @targetDeclName
  FILTER n.goalShapeHash == @goalShapeHash
  FILTER n.localContextHash == @localContextHash
  RETURN n
```

Collection names may evolve, but the query families should remain stable.

## 14. Safety and unknown-state discipline

Unknown means unknown.

If retrieval fails, record retrieval failure.

If InfoTree projection leaks a field, record leakage.

If the LSP times out, record timeout.

If a shape hash is approximate, mark it approximate.

If a theorem is only suggested by graph proximity, it must become a Lean
hypothesis field or witness structure before any theorem depends on it.

The orchestrator's central invariant is:

```text
No silent promotion of heuristic signal to proof truth.
```

