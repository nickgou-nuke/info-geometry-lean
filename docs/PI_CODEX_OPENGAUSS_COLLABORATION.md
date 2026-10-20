# Pi/Archon ↔ Codex collaboration under OpenGauss

## Purpose

This document proposes a safe integration between the Pi/Archon workflow and
the native Codex agent-team API. It is an implementation design, not evidence
that a direct Pi-to-`collaboration.spawn_agent` bridge already exists.

The repository has three distinct runtimes:

1. **Pi/Archon** — YAML workflows and provider nodes.
2. **Native Codex teams** — the session API
   `collaboration.spawn_agent`, `send_message`, `followup_task`, and
   `wait_agent`.
3. **Hive** — persistent task packets, leases, and worker state.

One theorem task must have one active scheduler. Do not run Archon, Hive, and a
manual Codex coordinator against the same task concurrently.

## Recommended packet flow

```text
Pi/Archon intake
  → bounded OpenGauss task packet
  → Codex adapter claim
  → native Codex scout/prover/refuter team
  → coordinator applies reviewed source patch
  → serial Lean and QMS gates
  → independent auditor and QA agent
  → Archon receives an evidence packet
```

The adapter is the missing component. It must be explicit, versioned, and
file-backed. It must not pretend that a provider response is a native Codex
subagent or that a workflow node is an independent audit.

## Task packet contract

Each packet should contain:

```json
{
  "schema": "opengauss.codex.packet.v1",
  "task_id": "stable-id",
  "owner_files": ["lean/InfoGeometry/Owner.lean"],
  "sandbox_root": "tmp/opengauss/<task-id>",
  "theorem_contract": {
    "carrier": "exact Lean type",
    "hypotheses": ["explicit assumptions"],
    "conclusion": "exact proposition",
    "non_claims": ["scope excluded from the theorem"]
  },
  "roles": {
    "scout": "read-only source search",
    "prover": "new-file candidate proof",
    "refuter": "independent counterexample and vacuity audit",
    "auditor": "final-diff review",
    "qa": "independent rerun of decisive checks"
  },
  "status": "queued"
}
```

The packet should reference owner declarations and exact source hashes. A
prompt, summary, or graph edge cannot substitute for the theorem contract.

## Role separation

### Scout

- Reads all relevant repository-owned Lean files and imports.
- Reports exact declarations, carriers, hypotheses, and dependents.
- Does not edit source.

### Prover

- Works only in `sandbox_root` or a newly created proposal file.
- Does not rewrite an existing owner file.
- Supplies a full proof or a precise obstruction.

### Refuter

- Receives the theorem contract independently.
- Searches for missing hypotheses, vacuity, false generality, carrier changes,
  and T16 scalar proxies.
- Must not rely on the prover's narrative.

### Integrator

- The coordinating Codex agent inspects the scout, prover, and refuter outputs.
- It alone applies an accepted edit to the owner layer.
- It preserves unrelated staged and unstaged work.

### Auditor and QA

- Auditor and QA must be distinct from the author and from each other.
- Auditor reviews the exact final diff.
- QA reruns Lean, build, placeholder, vacuity, and axiom checks from the
  checked-out source rather than trusting reports.

## Archon workflow shape

An Archon workflow may invoke Codex provider nodes explicitly:

```yaml
name: opengauss-codex-cycle
provider: codex
model: gpt-5.3-codex
modelReasoningEffort: high

nodes:
  - id: scout
    command: opengauss-scout
  - id: contract
    command: opengauss-contract
    depends_on: [scout]
  - id: candidate
    command: opengauss-candidate
    depends_on: [contract]
  - id: refute
    command: opengauss-refute
    depends_on: [contract]
  - id: kernel-check
    bash: |
      lake env lean "$OWNER_FILE"
    depends_on: [candidate, refute]
  - id: locked-build
    bash: |
      python3 tools/infra/run_locked_lake_build.py \
        --wait-for-build-lock "$TARGET"
    depends_on: [kernel-check]
  - id: audit
    command: opengauss-audit
    depends_on: [locked-build]
  - id: qa
    command: opengauss-qa
    depends_on: [audit]
```

The exact command names must be implemented and validated before being placed
in a production workflow. Deterministic checks belong in Bash/Python nodes;
model nodes may suggest or inspect but cannot certify.

## Native Codex adapter design

The adapter should:

1. Claim one packet using an atomic lease.
2. Build a bounded context packet from the current owner files.
3. Start separate Codex contexts for scout, prover, refuter, auditor, and QA.
4. Store each response with task ID, role, timestamp, source hashes, and status.
5. Return candidate source only under the sandbox directory.
6. Require the coordinator to apply any owner edit explicitly.
7. Release or requeue the packet on failure; never silently mark it complete.

The adapter must not attempt to call the session-only `spawn_agent` API from a
shell script. If native Codex teams are required, the active Codex coordinator
must create them, or a separately implemented Codex execution service must
expose a documented API.

## Acceptance gates

The OpenGauss cycle closes only after all of the following are recorded:

- source-grounded theorem contract;
- owner and import search;
- candidate proof with no `sorry`, `admit`, or custom axiom;
- independent refuter disposition;
- `lake env lean` result;
- serial locked build result;
- placeholder and semantic-vacuity scans;
- exact `#print axioms` output;
- independent auditor disposition;
- independent QA rerun;
- remaining scope and rejected claims.

Successful compilation is necessary but does not establish that the prose
interpretation matches the Lean theorem. Algebraic, topological, colimit,
completion, and physical claims require their own carriers and compatibility
proofs.

## Queue and artifact layout

Use one task queue and keep generated runtime state separate from source:

```text
task_queue.json
tmp/opengauss/<task-id>/
proofs/<task-id>.lean
proofs/<task-id>.sp
artifacts/opengauss/<task-id>/scout.json
artifacts/opengauss/<task-id>/refuter.json
artifacts/opengauss/<task-id>/audit.json
artifacts/opengauss/<task-id>/qa.json
```

Generated artifacts are evidence. They do not become theorem authority until
the corresponding Lean source is checked and the acceptance gates are closed.

## Proposed implementation order

1. Define the packet schema and atomic lease operations.
2. Add a read-only Pi/Archon exporter for one bounded task.
3. Add a Codex adapter that returns sandbox proposals only.
4. Add deterministic Lean and QMS gate commands.
5. Add distinct auditor and QA contexts.
6. Add requeue, timeout, and failure reporting.
7. Pilot on one finite theorem before enabling colimit, topology, or analytic
   tasks.

Until these pieces exist and are tested, Pi should use Archon Codex provider
nodes as a sequential workflow and should not claim to have launched a native
Codex swarm.
