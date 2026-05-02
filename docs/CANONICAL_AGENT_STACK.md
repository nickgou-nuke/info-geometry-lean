# Canonical Agent Stack

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines the canonical layered architecture for the local
agentic theorem factory.

It exists to stop terminology drift between:

- `NemoClaw`
- `OpenClaw`
- `OpenShell`
- `Hermes`
- `Codex CLI`
- `Gemini CLI`
- `LeanDojo-v2`
- local prover endpoints
- Lean/Lake closure

For host-level local model residency and scarce-GPU scheduling policy, see:

- [DGX_SPARK_MODEL_SCHEDULING_POLICY.md](./DGX_SPARK_MODEL_SCHEDULING_POLICY.md)
- [HERMES_OPERATOR_CHARTER.md](./HERMES_OPERATOR_CHARTER.md)
- [HERMES_BOUNDED_LOOP.md](./HERMES_BOUNDED_LOOP.md)

## 1. Canonical Stack

The canonical stack is:

`NemoClaw -> OpenClaw -> OpenShell -> { Hermes/Nemotron -> (DeepSeek / Goedel / Gemini / Codex / LeanDojo-v2) } -> Lean`

Read this in layers, not as one undifferentiated system.

## Current Operational Snapshot

This is the live host mapping as of the current DGX Spark setup:

- `Hermes` is installed and is the bounded orchestrator.
- `OpenClaw` now uses `openai-codex/gpt-5.4` as its large-context primary
  interactive model.
- `Gemini CLI` is installed but treated as explicit-operator-use only, not an
  automatic OpenClaw sidecar, because Gemini/Antigravity OAuth quota
  piggybacking has been subject to provider enforcement.
- Agent Gemini CLI calls must go through `tools/infra/run_gemini_guarded.sh`;
  this makes Gemini an irregular, jittered "dreaming sidecar" rather than a
  polling backend. Direct `gemini` use is operator-only.
- local `Qwen 35B` is the active SparkRun planner lane when resident:
  - `http://127.0.0.1:8000/v1`
  - `Qwen/Qwen3.6-35B-A3B-FP8`
- `DeepSeek-Prover-V2-7B` is the Lean4 proof-specialist lane:
  - `http://127.0.0.1:30002/v1`
  - `deepseek-prover-v2-7b-q8_0.gguf`
- `Goedel-Prover-SFT` is the conservative audit lane:
  - `http://127.0.0.1:30001/v1`
  - `Goedel-Prover-SFT.Q8_0.gguf`
- `Codex CLI` is the execution surface when explicitly routed.
- `LeanDojo-v2` is installed and currently wired through the token-free
  `LeanProgress -> Hermes packets` lane.
- Token-free proof-state/tactic probing is active through
  `tools/infra/lean_interact_wrapper.py`, which calls the repo-pinned
  `lake env lean` toolchain and returns JSON packets for Hermes/OpenClaw.
- `Lean 4.28.0` and `lake` are the final authority.
- `hermes-info-geometry-loop.timer` runs the bounded non-mutating planning
  loop.

## 2. Official NVIDIA Core

### NemoClaw

Role:

- reference stack
- lifecycle/control envelope
- managed wrapper for always-on assistants

Responsibilities:

- install and manage the `OpenShell` runtime
- simplify secure deployment of `OpenClaw`
- provide the secure control envelope for local agent execution

This is the outer operational shell, not the mathematical authority.

Reference:

- NVIDIA describes `NemoClaw` as an open source reference stack that
  simplifies running `OpenClaw` assistants and installs `OpenShell` for
  policy-based privacy and security guardrails.

Source:

- [NVIDIA NemoClaw](https://build.nvidia.com/nemoclaw)
- [NVIDIA/NemoClaw GitHub](https://github.com/NVIDIA/NemoClaw)

### OpenClaw

Role:

- assistant layer
- conversation and long-running agent surface

Current host state:

- `OpenClaw` CLI is installed and available on host `PATH`
- installed version is `2026.4.15`
- local state lives under `/home/goutev/.openclaw`
- local gateway service is installed as
  `/home/goutev/.config/systemd/user/openclaw-gateway.service`
- gateway currently runs on loopback port `18789`
- current primary model is the OAuth-backed large-context OpenAI/Codex provider
  `openai-codex/gpt-5.4`
- local Qwen 35B is the current on-host planner lane when the SparkRun resident is active

Responsibilities:

- host the conversational/agent UX
- expose the always-on assistant runtime
- sit inside the `NemoClaw/OpenShell` managed envelope

OpenClaw is the shell the user talks to, not the theorem authority.

Source:

- [OpenClaw on DGX Spark](https://build.nvidia.com/spark/openclaw/instructions)

### OpenShell

Role:

- secure runtime substrate
- sandbox / policy / guarded execution layer

Responsibilities:

- enforce execution controls
- manage provider routing
- provide the secure environment in which claws run

OpenShell is not the planner, not the prover, and not the verifier.

## 3. Custom Spire Extension Inside The NVIDIA Envelope

The theorem factory lives *inside* the `NemoClaw/OpenClaw/OpenShell` envelope.

### Hermes

Role:

- swarm manager
- top-level orchestrator

Current host state:

- official `Hermes Agent` is installed under `/home/goutev/.hermes/hermes-agent`
- CLI launcher is symlinked at `/home/goutev/.local/bin/hermes`
- current planner config points at the local `Qwen 35B` SparkRun endpoint for
  the active on-host planner lane
- interactive OpenClaw planning still uses `openai-codex/gpt-5.4` as the
  large-context primary interactive model
- local Qwen 35B base URL is `http://127.0.0.1:8000/v1`
- current Hermes CLI `context_length` override is `64000` to pass Hermes'
  startup guard
- current Qwen 35B server context is `32768`; it is the active local planner
  resident when the SparkRun lane is up
- current local execution cwd is `/home/goutev/repos/info-geometry-lean`

Responsibilities:

- decompose theorem/research tasks
- choose which lane handles each subtask
- maintain memory and provisional skills
- decide when execution is necessary
- control retries, escalation, and packet routing

Hermes may:

- plan
- route
- remember
- create provisional skills
- call for execution

Hermes may not:

- certify theorem truth
- bypass architecture placement
- bypass closure gates
- mutate canonical theorem statements directly

Operational note:

- Hermes is now installed and runnable on the host
- it is not yet the fully wired caretaker state machine for canonical repo
  admission
- it should currently be treated as the live orchestration surface above local
  prover lanes and below the NVIDIA envelope

### Codex CLI

Role:

- primary executor

Responsibilities:

- edit files
- run `lake`
- run DAG tooling
- run policy gates
- perform compilation and closure-facing actions

Policy:

- `Codex CLI` executes only when Hermes decides execution is required
- `Codex CLI` is not the top-level planner

### Gemini CLI

Role:

- explicit-operator-use broad elaboration and creative research sidecar

Responsibilities:

- upstream deep research
- Socratic expansion
- bridge ideation
- speculative packet drafting
- first-pass long-context elaboration before Codex/Nemotron/Goedel compression,
  but only when the operator explicitly requests Gemini CLI use
- must not use Antigravity OAuth extraction, token harvesting, proxying, or
  third-party quota piggybacking
- agents must invoke through `tools/infra/run_gemini_guarded.sh`
- direct `gemini` use is operator-only
- must remain irregular and infrequent; no periodic Gemini polling

Policy:

- useful for exploration
- not a truth surface
- not a closure surface

### LeanDojo-v2

Role:

- proving/data substrate

Responsibilities:

- theorem tracing
- proof-state extraction
- retrieval corpus generation
- prover benchmarking
- optional interactive proving substrate

Policy:

- not the orchestrator
- not the architecture governor
- not the final verifier

See also:

- [LEANDOJO_V2_INTEGRATION_BLUEPRINT.md](./LEANDOJO_V2_INTEGRATION_BLUEPRINT.md)

## 4. Specialist Model Lanes

### DeepSeek-Prover-V2-7B

Role:

- primary Socratic proof exploration lane

Use:

- dialogue about proof state
- local theorem search
- tactic/proof ideation
- intermediate proof repair loops

### Goedel

Role:

- conservative audit/system lane

Use:

- tighter report-style reasoning
- audit summaries
- fallback local reasoning lane

### Nemotron

Role:

- compact local planner/adjudication lane for bounded Hermes cycles

Use:

- short decomposition
- compact orchestration checks
- route selection
- local retry strategy
- non-mutating planning cycles

Nemotron is no longer the primary long-context OpenClaw planner. It remains a
local lane for short bounded cycles and focused summaries.

### Future Specialist Lanes

As they become healthy/available:

- `BFS-Prover-V2`
- `Goedel-Prover-V2`
- `Kimina`

These are specialist workers, not the orchestrator.

## 5. Final Authority Layer

### Lean / Lake

Role:

- final authority

Responsibilities:

- compile `.lean` truth surfaces
- reject invalid candidates
- define closure success

Trust order:

1. Lean source + Lean kernel
2. maintained closure gates
3. orchestration and retrieval lanes
4. research and exploration lanes

No agent, shell, or model may overrule Lean.

## 6. Canonical Request Flow

The canonical theorem-factory loop is:

1. User interacts with `OpenClaw`
2. `NemoClaw/OpenShell` provide the secure runtime envelope
3. `OpenClaw` uses `openai-codex/gpt-5.4` for large-context interactive planning
4. `Hermes` receives bounded packet tasks and may use local `Nemotron` for compact route selection
5. `Hermes` routes proof-local exploration to `DeepSeek`
6. `Hermes` may route broad elaboration to `Gemini CLI` only after explicit operator request
7. `Hermes` may route proof-state work to `LeanDojo-v2`
8. `Hermes` invokes `Codex CLI` only when execution/build/gates are needed
9. `Goedel` may be used as a conservative audit lane
10. `Lean` and `lake` decide the outcome

## 7. Non-Goals

This stack should **not** collapse into:

- `OpenClaw` as theorem prover
- `Codex CLI` as permanent top-level planner
- `Hermes` directly editing canonical files
- `LeanDojo-v2` becoming the orchestrator
- one generic local model handling all prompt classes

## 8. Local Working Mapping

Current intended local mapping on this host:

- `Hermes`
  - bounded orchestrator; compact timer cycles may use local `Nemotron`
- `OpenClaw`
  - interactive large-context surface using `openai-codex/gpt-5.4`
- `DeepSeek-Prover-V2-7B`
  - proof-specialist dialogue lane
- `Goedel`
  - audit lane
- `Codex CLI`
  - execution lane
- `Gemini CLI`
  - optional research sidecar
- `LeanDojo-v2`
  - installed token-free proving/data substrate
- `Lean 4.28.0`
  - authority layer

## 9. Canonical Rule

The canonical rule for this repository is:

- NVIDIA provides the secure agent envelope
- Hermes manages the proving swarm
- specialist models do specialist work
- Codex executes when routed
- Lean decides truth
