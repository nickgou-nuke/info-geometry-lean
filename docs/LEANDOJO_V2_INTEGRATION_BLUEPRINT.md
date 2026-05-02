# LeanDojo-v2 Integration Blueprint

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document defines how `LeanDojo-v2` fits into the repository's theorem
factory.

It is a proving/data substrate, not the top-level orchestrator.

## Role

`LeanDojo-v2` should be used for:

- theorem tracing
- proof-state extraction
- retrieval corpus generation
- prover benchmarking
- optional interactive proving substrate

It should **not** be used as:

- the top-level orchestrator
- the architecture governor
- the publish/closure authority
- the truth surface

Lean source and the Lean kernel remain the authority surface.

## Stack Placement

The intended local stack is:

1. `Hermes`
   - swarm manager
2. `Codex CLI`
   - executor
3. `Gemini CLI`
   - optional research sidecar
4. `OpenShell`
   - sandbox/gateway layer
5. `LeanDojo-v2`
   - proving/data substrate
6. `Lean`
   - final authority

This means:

- `Hermes` still manages routing
- `Codex CLI` still performs repo-native execution
- `LeanDojo-v2` supplies grounded proof/data lanes
- `Lean` still decides truth

Current Hermes host note:

- official `Hermes Agent` is installed in `/home/goutev/.hermes/hermes-agent`
- the live Hermes config currently points at local `Nemotron` on
  `http://127.0.0.1:30000/v1`
- local `DeepSeek` remains the proof-specialist lane on
  `http://127.0.0.1:30002/v1`
- Hermes local execution cwd is currently
  `/home/goutev/repos/info-geometry-lean`

## Current Host State

`LeanDojo-v2` is installed on this host in:

- `/home/goutev/lean-dojo-venv`

Verified facts:

- package name: `lean-dojo-v2`
- version: `1.0.6`
- import name: `lean_dojo_v2`

Important:

- the import name is **not** `lean_dojo`
- the default install currently brings in a heavy training-oriented dependency
  stack, including `torch`, `deepspeed`, `ray`, `transformers`, `trl`, and
  related packages

So the correct reading is:

- `LeanDojo-v2` is installed and importable
- it is wired into a token-free repo-native orchestration entrypoint through
  local `LeanProgress -> Hermes packets`
- deeper LeanDojo APIs still require credentials and a hardened bridge

## Current Repo-Native Entry Point

The first maintained repo-native LeanDojo entrypoint is:

- `tools/infra/leandojo_probe.py`

Purpose:

- validate that the dedicated LeanDojo env is usable
- confirm Lean/Lake visibility from the repo
- confirm the package import surface
- record operational blockers before deeper integration

Current emitted artifact:

- `artifacts/leandojo/probe.json`

Current observed constraint:

- the deeper interaction/data-extraction module
  `lean_dojo_v2.lean_dojo`
  currently raises unless `GITHUB_ACCESS_TOKEN` is set

That means:

- basic package presence is confirmed
- deeper LeanDojo tracing/integration is not yet token-free on this host

Example usage:

```bash
export PATH="$HOME/.elan/bin:$PATH"
source /home/goutev/lean-dojo-venv/bin/activate
cd /home/goutev/repos/info-geometry-lean
python tools/infra/leandojo_probe.py
```

## Token-Free Local Surface

Before credentials are present, the maintained token-free LeanDojo entrypoint is:

- `tools/infra/leandojo_token_free.py`

Purpose:

- validate the safe local `LeanDojo-v2` import surface
- record which submodules are currently usable without credentials
- surface bundled `external_api` Lean files
- emit a local sample `LeanProgress` dataset

Current emitted artifacts:

- `artifacts/leandojo/token_free_surface.json`
- `artifacts/leandojo/lean_progress_sample.jsonl`

Current safe surface on this host:

- `lean_dojo_v2`
- `lean_dojo_v2.lean_progress`
- `lean_dojo_v2.lean_progress.create_sample_dataset`
- bundled files under `lean_dojo_v2/external_api/`

Current blocked surface without credentials:

- `lean_dojo_v2.lean_dojo`
- `lean_dojo_v2.database`
- `lean_dojo_v2.lean_agent`
- `lean_dojo_v2.utils`

Example usage:

```bash
source /home/goutev/lean-dojo-venv/bin/activate
cd /home/goutev/repos/info-geometry-lean
python tools/infra/leandojo_token_free.py --write-sample-dataset
```

## LeanProgress To Hermes Packet Lane

The first actual bridge from token-free LeanDojo data into the existing Hermes
handoff contract is:

- `tools/infra/leandojo_to_hermes_packets.py`

Purpose:

- read local LeanProgress-style JSONL rows
- convert them into valid Hermes research packets
- write them under Hermes' packet lane

Current output location:

- `quarantine/hermes_memory/research_packets/`

Current manifest:

- `quarantine/hermes_memory/research_packets/leanprogress_manifest.json`

Current behavior:

- each LeanProgress row becomes one packet
- packets are marked `files`-only provenance
- packets remain `draft`
- tactic text is treated as candidate evidence, not closure
- `sorry`-bearing rows remain quarantine-only via explicit forbidden moves

Example usage:

```bash
export PATH="$HOME/.elan/bin:$PATH"
source /home/goutev/lean-dojo-venv/bin/activate
cd /home/goutev/repos/info-geometry-lean
python tools/infra/leandojo_to_hermes_packets.py
```

## Environment Strategy

Keep `LeanDojo-v2` isolated from the general repo Python lane.

Recommended env split:

- `/home/goutev/venv-goedel`
  - general repo orchestration/python lane
- `/home/goutev/llama-cpp-venv`
  - model-serving helpers
- `/home/goutev/lean-dojo-venv`
  - dedicated LeanDojo-v2 lane

This avoids contaminating the general repo environment with heavy theorem/training
dependencies.

## Recommended Responsibilities

Use `LeanDojo-v2` for:

- trace export into repo-local artifacts
- proof-state retrieval for Hermes/OpenClaw loops
- retrieval dataset generation
- local prover evaluation

Do not use it for:

- theorem placement
- policy adjudication
- final closure claims

## Suggested Artifact Roots

- `artifacts/leandojo/trace/`
- `artifacts/leandojo/retrieval/`
- `artifacts/leandojo/bench/`

## Next Integration Step

The repo now has a token-free proof-state/tactic probe:

- `tools/infra/lean_interact_wrapper.py`

It uses the pinned repo toolchain through `lake env lean`, constructs a
temporary Lean theorem for a supplied goal, emits `trace_state`, applies an
optional tactic, and returns deterministic JSON.  This gives Hermes/OpenClaw a
token-free proof-state/tactic interaction surface without requiring GitHub API
credentials or treating sample data as closure evidence.

Examples:

```bash
.venv-py312/bin/python tools/infra/lean_interact_wrapper.py \
  --goal '1 = 1' --import Init --timeout 30

.venv-py312/bin/python tools/infra/lean_interact_wrapper.py \
  --tactic '1 = 1' 'rfl' --import Init --timeout 30
```

The next deeper repo-native step is:

1. connect this probe to real target theorem manifests
2. trace or query a target theorem/file through the dedicated LeanDojo-v2 lane
3. emit deterministic artifacts under `artifacts/leandojo/`
4. feed those outputs back into the existing Hermes packet loop

That is the shortest path from "installed" to "operationally useful".
