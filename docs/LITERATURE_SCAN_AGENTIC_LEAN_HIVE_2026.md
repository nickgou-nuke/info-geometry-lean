# Literature and upstream scan: agentic Lean, Hive, Pantograph, and OpenGauss

## Scope and evidence boundary

This is a live upstream/literature scan for repository design decisions. Web
metadata and arXiv abstracts are navigation evidence, not proof authority. No
external result establishes a theorem in this repository. Lean kernel output,
locked builds, and independent audit remain decisive.

The GitHub and arXiv endpoints used for this scan returned dates in October
2026. arXiv entries below are preprints unless independently published.

## OpenGauss

Repository: <https://github.com/math-inc/OpenGauss>

The public README describes OpenGauss as a project-scoped Lean workflow
orchestrator. Its relevant features include:

- project registration and active-project isolation;
- managed child-agent sessions;
- proving, review, checkpoint, formalization, and refactoring workflows;
- Codex and Claude backends;
- swarm tracking and recovery.

The repository's current direction is therefore consistent with using the
OpenGauss project/session ID as the root of Hive lineage. OpenGauss remains an
orchestrator and workflow frontend; it is not a replacement for Lean kernel
checking or an independent proof auditor.

A recent public commit observed during the scan was
`f87633900ae185b8037bf451a914fe7eeae1eb08`, dated 2026-04-05. The repository
had no stable release result from the queried GitHub releases endpoint, so a
moving checkout must not be treated as a pinned dependency without recording
its commit.

## Pantograph

Repository: <https://github.com/leanprover/Pantograph>

Latest upstream `dev` commit observed:

```text
0ee70917fb93a5421157119362ecde806a4d881b
2026-10-20
```

Pantograph provides a machine-to-machine Lean frontend, including:

- REPL proof execution;
- expression construction;
- environment inspection;
- Lean frontend interaction;
- a library/FFI interface.

Upstream README: <https://github.com/leanprover/Pantograph/blob/dev/README.md>

No stable GitHub release was returned. The repository's current checkout is
therefore best treated as an exploratory frontend pinned by commit and
compatible toolchain, not as an authority layer.

Repository integration rule:

```text
contract + owner/source hashes
  → Pantograph exploration
  → sandbox candidate
  → lake env lean
  → locked build/audit/QA
```

A Pantograph session becomes stale when the contract hash or owner snapshot
hash changes. Pantograph output may suggest tactics or repairs, but it may not
raise packet authority or write an owner file.

## Lean and Lake

Latest upstream Lean releases observed:

- Lean `v4.35.0`: <https://github.com/leanprover/lean4/releases/tag/v4.35.0>
- Lean `v4.36.0-rc1`: <https://github.com/leanprover/lean4/releases/tag/v4.36.0-rc1>

This repository is pinned to Lean `v4.34.1`. The pilot must not upgrade the
pinned toolchain. `lake comparator --paranoid` was not found in the pinned
checkout during local inspection, so it remains an optional later experiment,
subject to explicit compatibility testing.

## ArangoDB

Upstream tags observed:

- `v3.12.12.1`
- `v3.12.12`

Repository Arango retrieval and graph similarity should remain navigation
infrastructure only. The three persistence lanes must not be merged:

```text
ARANGO_*       → AST/AQL declaration DAG
HIVE_ARANGO_*  → Hive queue, leases, workers, and packet lineage
agent memory   → retrieval/context only
```

A reachable DAG database does not prove that the Hive queue is reachable.
Health checks must report endpoint, database, schema, and credentials' lane
without exposing secrets.

## Recent formal-proof research

### Maestro

**Maestro: Agentic Formal Proof Development by Coordination**
<https://arxiv.org/abs/2610.25920>

The paper argues that proof failure should report its cause, not merely fail.
A coordinator can then distinguish insufficient guidance, false lemmas, and
bad decomposition, and replan globally. Repository consequence:
structured failure packets, refuters, bounded requeue, and lineage-aware
replanning are more valuable than blind repeated proof attempts.

### LeanPRM

**LeanPRM: Lean-Grounded Process Supervision for Natural Language Proof
Verification**
<https://arxiv.org/abs/2610.17697>

Lean is used to produce step-level labels for natural-language proof checking.
Repository consequence: proof-state and verifier evidence can be useful packet
artifacts, but learned supervision does not replace kernel verification.

### ProofGap

**ProofGap: Benchmarking Step-Level Formal Reasoning with Local Obligations**
<https://arxiv.org/abs/2609.29296>

The work isolates local proof gaps from end-to-end theorem composition.
Repository consequence: a finite local obligation is suitable for the first
pilot, but local success must not be promoted as whole-theorem completion
without the full source and build chain.

### AI Agent Swarms as Researchers

<https://arxiv.org/abs/2609.35719>

The paper emphasizes that agent output can outpace human review. Repository
consequence: independent auditor and QA contexts, immutable evidence, explicit
unresolved states, and refusal to promote model consensus are necessary.

### CPUNeSy

<https://arxiv.org/abs/2609.37490>

This work studies controlled writes to symbolic state and certificate gates.
Its stated limitation is important: a certificate validates a derivation
relative to admitted premises, while semantic faithfulness to the source can
remain conditional. Repository consequence:

```text
retrieval evidence ≠ theorem evidence
certificate ≠ semantic truth
provider output ≠ Lean proof
```

## Recommended repository pipeline

```text
OpenGauss session ID
  → GroundTruthTheoremContract
  → hash-bound Hive task
  → Pantograph exploration, if useful
  → sandbox candidate
  → independent refutation
  → Lean verification
  → serial locked build
  → independent audit
  → independent QA
  → promotion decision
```

Every task should reference, where applicable:

- OpenGauss project/session ID;
- theorem contract hash;
- owner-file hash;
- source snapshot hash;
- candidate hash;
- packet hash;
- Pantograph session ID;
- exact command and toolchain identity.

The first pilot should be one finite theorem, with no concurrent swarm and no
toolchain upgrade. It should exercise claim, heartbeat, artifact emission,
lease expiry, requeue, Lean verification, and audit before any promotion.
