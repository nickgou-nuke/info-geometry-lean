# DGX Spark Model Scheduling Policy

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines the scheduling policy for local model use on DGX Spark.

The central fact is simple:

- the local GPU is a scarce prover slot

The system must therefore schedule models, not merely collect them.

## 1. Core Rule

Treat DGX Spark local GPU residency as scarce.

Do **not** assume that all local models can remain hot simultaneously.

The default policy is:

- one heavy local model at a time
- optionally one additional small quantized prover only after empirical validation

## 2. Layer Separation

The scheduler must distinguish:

### Always-On Logical Components

These are allowed to remain active because they are not the scarce GPU resident:

- `Hermes`
  - orchestration logic
  - memory
  - routing
- `Codex CLI`
  - execution surface
- `Gemini CLI`
  - optional research sidecar
- `NemoClaw`
  - reference stack / lifecycle wrapper
- `OpenClaw`
  - assistant shell
- `OpenShell`
  - sandbox and gateway
- `Lean`
  - authority layer
- `ArangoDB`
  - persistence/query layer

### Scarce GPU-Resident Components

These are the actual residency budget:

- `DeepSeek-Prover-V2-7B`
- `Goedel-Prover-SFT`
- `Nemotron`
- `BFS-Prover-V2`
- `Goedel-Prover-V2`
- `Kimina`
- any local fine-tuned theorem-prover variants

## 3. Residency Classes

### Class A: Safe Default Residents

These are the most plausible always-usable local theorem workers:

- `DeepSeek-Prover-V2-7B`
- `Goedel-Prover-SFT`

Policy:

- either may be the active resident
- both together may be tested, but should not be assumed stable forever

### Class B: Heavy Residents

Examples:

- `Nemotron`
- `BFS-Prover-V2-32B`
- larger future planner/auditor models

Policy:

- one at a time
- mutually exclusive with other heavy residents
- should usually displace smaller workers only when their role is actually needed

### Class C: Variant/Fine-Tuned Residents

Examples:

- fine-tuned `DeepSeek-Prover-V2-7B`
- fine-tuned `Goedel`

Policy:

- possible to co-schedule with the matching small base family only after testing
- still treated as scarce

## 4. Default Runtime Policy

The default runtime policy for this repository is:

- `Hermes`
  - always active as orchestrator
- `Codex CLI`
  - invoked on demand
- `Gemini CLI`
  - invoked on demand
- `OpenClaw`
  - always-on shell if desired
- `DeepSeek-Prover-V2-7B`
  - default active proof dialogue lane
- `Goedel`
  - optional audit lane
- heavy models
  - on demand only

This means:

- the proving stack should usually start with the smallest sufficient local worker
- only escalate to heavier residents when a clear reason exists

## 5. Hermes Routing Rules

Hermes is responsible for choosing the lane.

### Default rule

Use the cheapest sufficient worker first.

Order:

1. `DeepSeek-Prover-V2-7B`
2. `Goedel`
3. `Gemini CLI` or `Codex CLI` sidecars when needed
4. heavy local resident only if the task justifies it

### For theorem exploration

Prefer:

- `DeepSeek-Prover-V2-7B`

### For conservative audit or report-style reasoning

Prefer:

- `Goedel`

### For upstream research/bridge ideation

Prefer:

- `Gemini CLI`

### For file mutation, builds, and gates

Prefer:

- `Codex CLI`

### For grounded proof-state or dataset work

Prefer:

- `LeanDojo-v2` lane once installed

### For final closure

Prefer:

- `Lean`
- `lake`

## 6. Mutual Exclusion Rules

The following should be treated as mutually exclusive unless the host is proven stable:

- `Nemotron` + any other heavy model
- `BFS-Prover-V2-32B` + any other heavy model
- multiple large planner/auditor models simultaneously

The following may be tested, but should not be assumed:

- `DeepSeek-Prover-V2-7B` + `Goedel`
- `DeepSeek-Prover-V2-7B` + fine-tuned `DeepSeek-Prover-V2-7B`

## 7. Activation Policy

The correct model lifecycle is:

1. Hermes selects the needed worker
2. if not resident, activate that model
3. run the assigned proving/audit task
4. return outputs to Hermes
5. unload or deprioritize the resident if a different heavy worker is needed

This policy is better than trying to keep every model loaded permanently.

## 8. Failure Policy

If a local model:

- fails to load
- becomes unhealthy
- exceeds memory budget
- destabilizes other workloads

then Hermes should:

1. mark the worker unavailable
2. route to the next cheaper viable worker
3. preserve diagnostics
4. avoid automatic repeated reload loops without new evidence

## 9. Practical Rule For This Host

Current intended working rule:

- `DeepSeek` is the default local proof worker
- `Goedel` is the optional audit worker
- `Nemotron` is not assumed always-on
- larger/future models are on-demand only

This host should be treated as:

- a machine with many possible backends
- but only one scarce active local GPU lane

## 10. Canonical Summary

The correct mental model is:

- not many always-running local models
- but many available backends and one scarce active local GPU slot

That is why `Hermes` matters:

- Hermes schedules workers
- Hermes does not require every worker to remain resident
- Hermes preserves system coherence under resource constraints
