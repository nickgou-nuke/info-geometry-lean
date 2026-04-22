# Theorem-Factory Systems Blueprint

> For Hermes: treat this as a systems architecture memo, not a claim that every listed subsystem already exists in the live repo. Lean remains the only truth authority.

## Goal

Define a grounded architecture for an `info-geometry-lean` theorem-factory that:
- uses Lean 4 as the sole proof/anti-proof truth gate,
- uses ArangoDB as a layered graph memory and navigation substrate,
- allows Hermes/OpenClaw-style agent swarms to cooperate without faking mathematical closure,
- and preserves a strict separation between verified fossils, open proof states, and compressed failure memory.

## Status Legend

- `LIVE`: present in the current repo/runtime.
- `DERIVABLE`: strongly suggested by current owner surfaces but not yet packaged.
- `SPECULATIVE`: architecture target only; not implemented.

---

## 1. Core System Principle

The theorem factory is organized by one invariant:

```text
LLM/pathos may propose.
Graph memory may retrieve.
Middleware may route.
Lean decides.
```

Nothing becomes canonical theorem memory unless Lean accepts it.

This implies four distinct roles:
1. `Generator` — produces candidate tactics/terms/questions.
2. `Extractor` — turns Lean proof state / declarations into canonical artifacts.
3. `Retriever` — searches graph/value memory for candidate actions.
4. `Kernelizer` — re-enters Lean and records `closed` / `applied` / `rejected`.

---

## 2. Live Substrates

### 2.1 Lean 4 proof authority
Status: `LIVE`

Lean and `lake` are the only trusted acceptance mechanisms.
Repo-local supporting surfaces already exist for proof-state and kernel interaction:
- `tools/infra/lean_interact_wrapper.py`
- `tests/test_lean_interact_wrapper.py`

### 2.2 ArangoDB graph substrate
Status: `LIVE`

The current database already contains substantial graph material, including:
- `raw_info_nodes`, `raw_info_edges`
- `raw_infotree_*`
- `topology_overlay`, `topology_overlay_edges`
- `arango_dag_components`, `arango_dag_component_edges`
- `arango_dag_impact`, `arango_dag_dominators`, `arango_dag_motifs`, `arango_dag_process_flows`

This is already enough for:
- SCC-first navigation,
- theorem-basin connectedness checks,
- raw-witness descent back into Lean source.

It is not yet a complete whole-repo vector+graph semantic memory over all docs, black books, packets, and artifacts.

### 2.3 Agent gateways / orchestrators
Status: `LIVE`

Local stack currently present:
- OpenClaw gateway service
- Hermes gateway service
- repo-side orchestration specs under `nemoclaw_config.yaml` and `tools/infra/hermes_config.yaml`

Live communication posture after reconfiguration:
- Hermes shared-room mode enabled via `~/.hermes/config.yaml`
- OpenClaw remains loopback + token-auth + tailscale-off

This gives freer local shared context without widening network exposure.

---

## 3. Memory Layers

The theorem factory should use four memory layers.

### 3.1 Logos Canon
Status: `DERIVABLE`

Canonical verified objects.
Examples:
- verified declarations,
- theorem conclusions,
- theorem-backed canonical constructors,
- audit-approved exact owner theorems.

Desired collection concept:
- `DiamondFossils`

Rules:
- append-only except for deduplication / supersession metadata,
- never sacrificed for popularity or low reuse,
- always tied to Lean-accepted evidence.

### 3.2 Open proof-state layer
Status: `DERIVABLE`

Artifacts for goals, local contexts, extracted `InfoTree` states, proof obligations.

Desired collection concept:
- `InfoTrees`

Rules:
- mutable,
- can be retried, branched, distilled, archived,
- not truth by itself.

### 3.3 Personal / project torsion
Status: `SPECULATIVE`

Private or scoped exploration memory for unfinished ideas, speculative tactics, and local drafts.

Rules:
- may be retained by scope,
- may be demoted or archived without global deletion,
- should not pollute canonical search by default.

### 3.4 Negative knowledge
Status: `DERIVABLE`

Compressed memory of repeated failure patterns, invalid re-entry attempts, and dead proof motifs.

Desired collection concept:
- `DeadEndMotifs`

Rules:
- should be produced by distillation, not manual rhetoric,
- useful as retrieval penalties or anti-patterns,
- never confused with proof.

---

## 4. Canonical Artifact Contract

The minimal viable theorem-factory should emit explicit typed artifacts.

### 4.1 Goal / proof-state artifact
Status: `SPECULATIVE` as a formal schema

```json
{
  "artifactKind": "InfoTreeArtifact",
  "space": "infotree",
  "module": "...",
  "goalIndex": 0,
  "targetPretty": "...",
  "canonicalPreimage": "...",
  "targetHashShape": "sha256:hive-v1:...",
  "targetHashExact": "sha256:hive-v1:...",
  "contextFingerprint": "sha256:hive-v1:...",
  "normalizationPolicy": "instantiateMVars+whnf(default)",
  "projectionPolicy": "preserve-proj",
  "hasUnassignedMVars": false
}
```

### 4.2 Verified declaration artifact
Status: `SPECULATIVE` as a formal schema

```json
{
  "artifactKind": "DiamondFossil",
  "space": "logos",
  "constName": "Nat.add_comm",
  "declarationKind": "theorem",
  "fullTypePretty": "...",
  "conclusionPretty": "...",
  "conclusionHashShape": "sha256:hive-v1:...",
  "conclusionHashExact": "sha256:hive-v1:...",
  "kernelStatus": "verified",
  "axiomsUsed": [],
  "environmentHash": "sha256:..."
}
```

### 4.3 Failed candidate artifact
Status: `SPECULATIVE` as a formal schema

```json
{
  "artifactKind": "FailedCandidate",
  "goalHash": "sha256:hive-v1:...",
  "candidateConstName": "Nat.add_comm",
  "failureKind": "ApplyFailed",
  "messageHash": "sha256:...",
  "karmicDebtDelta": 1
}
```

---

## 5. Lean-Side MVP Construction Order

This is the recommended build order for a real prototype.

### Phase 1A — Lean extractor
Status: `SPECULATIVE`, highest priority

Implement:
- canonical shape serialization,
- used-fvar-in-local-context-order abstraction,
- exact vs shape hash preimages,
- declaration conclusion extraction,
- projection / normalization policy stamping.

Target commands/tactics:
- `hive_probe`
- `#hive_index_decl`

### Phase 1B — Lean kernelizer
Status: `SPECULATIVE`, highest priority

Implement two re-entry tactics:
- `hive_try_const` — allow partial application, log remaining subgoals
- `hive_annihilate` — strict: only succeed if the goal is fully closed

Outcome states must be:
- `CLOSED`
- `APPLIED`
- `REFUSED`

### Phase 2 — Thin middleware
Status: `SPECULATIVE`

Use Rust (preferred) or a minimal Python bridge as a semantic firewall.
Responsibilities:
- parse Lean-emitted JSON lines,
- compute stable digests over Lean-emitted canonical bytes,
- upsert artifacts into ArangoDB,
- retrieve candidate const names / anti-patterns,
- never reinterpret Lean semantics independently.

### Phase 3 — Retrieval V-layer
Status: `SPECULATIVE`

Hybrid retrieval only:
1. exact hash
2. shape hash
3. subtree motif overlap
4. dense vector retrieval later
5. graph reranking
6. DeadEnd penalties

### Phase 4 — Distillation / negative memory
Status: `SPECULATIVE`

Repeated `REFUSED` events become:
- `DeadEndMotif`
- `TacticAntiPattern`
- `FailureSummary`

No artifact should be deleted before deciding whether it should instead be distilled.

---

## 6. Retrieval Layer Design

### 6.1 Exact retrieval is the spine
Status: `DERIVABLE`

Deterministic retrieval must remain primary:
- `targetHashExact`
- `targetHashShape`
- `conclusionHashExact`
- `conclusionHashShape`

### 6.2 Learned retrieval is peripheral
Status: `SPECULATIVE`

Dense retrieval may later expand recall, but must never replace exact identity.

Rule:

```text
Exact hash retrieval = spine.
Learned attention = peripheral nervous system.
Lean verification = immune system.
```

### 6.3 Symbolic tokenizer first
Status: `SPECULATIVE`

Use Lean canonical S-expressions as input, not pretty-printed text.
Start with symbolic tokenization:
- DFS tokens
- subtree motifs
- path tokens

Delay BPE/natural-language style tokenization.

---

## 7. Multi-User / Multi-Agent Memory Metabolism

### 7.1 Global truth must not be pruned
Status: `DERIVABLE`

Verified canonical fossils should not be metabolically deleted.
They may be:
- deduplicated,
- superseded,
- hidden by scope,
- marked stale by environment.

But not sacrificed because of popularity or budget pressure.

### 7.2 Scoped pruning for everything else
Status: `SPECULATIVE`

Use a retention lease / visibility model:
- user scope
- project scope
- global canon
- negative knowledge layer

MotherBee should demote/archive/distill before purging.

### 7.3 DeadEnd motifs as the Dirac Sea of antiproofs
Status: `DERIVABLE` conceptually, `SPECULATIVE` structurally

The anti-proof vacuum is a useful repo-native future layer.
It should store repeated rejected proof attempts and be used to penalize future retrievals for the same shape.

---

## 8. How This Maps to Existing Repo Concepts

### Already strongly aligned
- SCC-first theorem-basin navigation
- raw-witness descent
- owner / translator / coherence / capstone layering
- Lean as sole truth authority
- Pauli audit / anti-closure discipline
- graph-guided closure debt reduction
- Hestenes / Krein / operatorial representation ladders
- supergraded operatorial geometry
- operatorial Cramér–Rao / Onsager response corridors

### Not yet implemented but structurally compatible
- Hive probe / fossil indexer / annihilator tactics
- Rust MotherBee event spine
- explicit `DiamondFossils` / `DeadEndMotifs` collections
- retrieval penalties from negative knowledge
- scoped visibility-aware proof memory
- theorem-factory dashboard / “Hermes Lens”

---

## 9. Security / Communication Blueprint

### Live swarm posture now
Status: `LIVE`

- Hermes shared context in group/room mode: enabled
- OpenClaw gateway: still local and token-gated
- no public widening of the control plane

### Recommended communication posture
Status: `DERIVABLE`

- keep OpenClaw local-only unless a clearly verified Tailscale or equivalent private mesh is needed
- use Hermes as the logical broker for shared contexts and cron/workflow coordination
- use MCP/webhook/API-server patterns only after explicit scoped configuration
- do not equate “free swarm communication” with “public network exposure”

---

## 10. Immediate Construction Priorities

### Priority 1
Build the Lean-side tracer bullet:
- `hive_probe`
- `#hive_index_decl`
- `hive_try_const`
- `hive_annihilate`

### Priority 2
Freeze the event JSON contract and implement the thin middleware ingest loop.

### Priority 3
Store verified declaration conclusions and open goals in ArangoDB under a stable canonical hash contract.

### Priority 4
Add failed-candidate distillation into negative memory.

### Priority 5
Only then add dense/transformer retrieval and analogy engines.

---

## 11. Hard Rules

1. Do not let Python/Rust become a second Lean interpreter.
2. Do not let vector search replace exact canonical retrieval.
3. Do not let graph connectedness be mistaken for proof.
4. Do not let speculative architecture language masquerade as implemented repo state.
5. Do not promote anything to canonical memory unless Lean has accepted it.

---

## 12. Final Summary

The theorem factory should be built as a layered system:

```text
LLM swarm / pathos
  -> Lean extractor
  -> typed artifact/event contract
  -> Rust semantic firewall
  -> Arango theorem/proof-state manifold
  -> candidate retrieval
  -> Lean re-entry and verification
  -> verified fossil or distilled anti-proof
```

This is not yet fully implemented in the live repo.

But the repo already contains enough of the conceptual substrate — graph layers, theorem-basin navigation, operatorial representation ladders, truth-gate discipline, and orchestrator surfaces — that this blueprint is a legitimate next-stage systems architecture for the project.
