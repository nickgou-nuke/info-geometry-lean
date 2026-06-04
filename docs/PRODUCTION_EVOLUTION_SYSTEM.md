# Production Evolution System

Status: implemented in-repo as of 2026-06-03
Scope: autonomous skill evolution and proof-debt reduction for Lean closure work

## Purpose

This repository contains a real code path for autonomous skill evolution aimed at
closing Lean proof debt and detecting dishonest certificate-style proof surfaces.
The production loop is not a vague concept document: the core pieces are present
under `tools/infra/`, there is a worker entrypoint, a systemd unit, a grounded
real-evaluation harness, a proof-repair escalation lane, and a critic that can
extend anti-pattern coverage.

The loop operates on skills such as:
- `skills/audit-proof/SKILL.md`
- `skills/closure-debt-proof/SKILL.md`

Related policy documents:
- `docs/codex/codex.md`
- `docs/GOAL_LOOP_SOP.md`

## High-Level Architecture

```text
Arango skill-evolution queue
  -> evolution_worker.py claims task
  -> gepa_evolver.py mutates a skill body with DSPy GEPA
  -> gepa_real_eval.py evaluates the mutated skill on real repo tasks
  -> proof_seeker.py escalates failed tasks through audit / coding / search lanes
  -> vacuity_critic.py extracts new obfuscation patterns from failures
  -> evolved variants are archived under quarantine/hermes_skills/
  -> worker repeats on the next queued evolution task
```

This is the implementation-level division of responsibility currently reflected
in the codebase. It is the authoritative architecture for the evolution lane.

## Concrete Components

### 1. Evolution Worker

Primary files:
- `tools/infra/evolution_worker.py`
- `tools/infra/evolution-worker.service`

Responsibilities implemented today:
- polls the Arango queue named `skill-evolution`
- claims tasks with lease/worker bookkeeping
- loads the requested skill from `skills/<skill-name>/SKILL.md`
- finds real evaluation tasks from the repository
- runs GEPA evolution
- persists evolved skill variants under `quarantine/hermes_skills/evolved/`
- records lineage / archive information
- invokes proof-seeking and critic passes on non-perfect results

Important implementation constants in `evolution_worker.py`:
- `POLL_INTERVAL = 5`
- `LEASE_SECONDS = 1800`
- `WORKER_ID = "evolution-worker-autonomous"`
- `EVOLUTION_QUEUE = "skill-evolution"`

The checked-in systemd unit wires the worker to this repository checkout and the
local Python environment.

### 2. GEPA Skill Evolution

Primary file:
- `tools/infra/gepa_evolver.py`

What it actually does:
- treats the skill body text as the optimized parameter
- uses `dspy.GEPA` to mutate predictor instructions
- loads credentials from `~/.hermes/.env` when available
- prefers DeepSeek for reflection if `DEEPSEEK_API_KEY` is present
- otherwise falls back to OpenRouter
- can use a normal metric or a grounded `RealEvaluator`
- extracts the evolved instructions back into skill text
- archives variants for rollback and lineage review

Archive / rollback surfaces:
- `quarantine/hermes_skills/archive/<skill-name>/manifest.jsonl`
- `quarantine/hermes_skills/archive/<skill-name>/gen_*.md`

Important design fact:
GEPA is not optimizing theorem statements directly. It is optimizing skill
instructions, and those instructions are then judged by grounded execution.

### 3. Real Evaluator

Primary file:
- `tools/infra/gepa_real_eval.py`

What it actually measures:
- runs Hermes against real repo tasks
- checks whether the targeted debt surface was removed or improved
- optionally compiles with `lake env lean`
- restores originals after evaluation
- supports isolated temp-copy evaluation by default
- caches evaluation results under the quarantine tree

Key data structures implemented there:
- `EvalTask`
- `TaskResult`
- `EvalResult`
- `RealEvaluator`

Important behavioral fact:
The evaluator is grounded in file edits plus compiler feedback, not text-only
self-scoring.

Related fitness scorer:
- `tools/infra/evolution_evaluator.py`

This is a separate Arango-backed scoring surface. It computes fitness from task
outcomes and failure patterns; it is not the same thing as the grounded
file-edit harness in `gepa_real_eval.py`.

### 4. Proof Seeker Escalation Lane

Primary file:
- `tools/infra/proof_seeker.py`

This is the current multi-lane recovery / escalation surface when the evolved
skill does not fully solve a task.

The implemented lanes are:
1. mathlib / LeanSearch / Loogle style search surfaces
2. Alexandria / external corpus search
3. arXiv search
4. direct coding-agent digestion / formalization
5. ChatGPT audit via browser-harness / CDP

Operationally relevant facts from the implementation:
- the direct coding lane loads `audit-proof` and `closure-debt-proof`
- the coding lane uses the Pi CLI with DeepSeek (`deepseek-v4-flash`)
- the audit lane preserves browser-chat context across retries
- candidate proofs are compiled back against the repository

The worker currently uses ProofSeeker in a staged way after an imperfect
GEPA/evaluation cycle.

Auxiliary browser harness:
- `tools/infra/chatgpt_browser_harness_driver.py`

This is the automation layer used by the Stage 0 ChatGPT audit lane. It is a
sidecar for proposal generation, not a proof authority.

### 5. Vacuity Critic

Primary file:
- `tools/infra/vacuity_critic.py`

Purpose:
- inspect failed evaluations
- discover new naming synonyms for dishonest certificate-style proof surfaces
- expand anti-pattern coverage
- optionally extend a skill file's anti-pattern section

Built-in pattern coverage is currently bootstrapped from code in
`VacuityCritic.BASE_PATTERNS`, including:
- `_True`
- `_sorryProof`
- `_certificate`
- `_valid`
- `_witness`
- `_bridge`

Important reality check:
The critic's default schema path is coded as
`tools/schema/vacuity/certificate_patterns.json`, but this repository's current
production authority is the critic implementation itself plus the skill files;
that schema file is not the only source of truth and may be absent until the
critic writes it.

### 6. Mission Loop

Primary file:
- `tools/infra/mission_loop.py`

This is the higher-level mission orchestration wrapper around the queue-worker
and skill-evolution loop. It coordinates the mission, but it is still a control
surface over the same grounded proof/evolution pieces above.

## Runtime Data Flow

### Queue Input

The worker expects evolution tasks in the Arango queue `skill-evolution`.
Tasks can be enqueued through the helper in `evolution_worker.py`.

### Skill Source

The worker reads from:
- `skills/<skill-name>/SKILL.md`

### Evolved Output

The worker writes to:
- `quarantine/hermes_skills/evolved/<skill-name>/autoevolved_<timestamp>.md`

### Archive / Lineage Output

GEPA archives rollback candidates under:
- `quarantine/hermes_skills/archive/<skill-name>/`

### Evaluation Cache

Real-eval cache path:
- `quarantine/hermes_skills/evolved/.eval_cache.jsonl`

## Operational Commands

### Run one worker cycle in foreground

```bash
python3 tools/infra/evolution_worker.py --once
```

### Run the worker continuously

```bash
python3 tools/infra/evolution_worker.py
```

### Enqueue an evolution task

```bash
python3 tools/infra/evolution_worker.py --enqueue audit-proof 10
python3 tools/infra/evolution_worker.py --enqueue closure-debt-proof 5
```

### Run GEPA directly

```bash
python3 tools/infra/gepa_evolver.py --skill lean-proof --generations 5
```

### Run the real evaluator directly

```bash
python3 tools/infra/gepa_real_eval.py \
  --skill quarantine/hermes_skills/evolved/lean-proof/gepa_evolved_example.md \
  --tasks-file tasks.jsonl
```

### Run the critic directly

```bash
python3 tools/infra/vacuity_critic.py \
  --failed-tasks artifacts/eval_failures.jsonl \
  --skill skills/closure-debt-proof/SKILL.md \
  --update-skill
```

### Run proof search / proof escalation directly

```bash
python3 tools/infra/proof_seeker.py \
  --target "jones_eq_coeff_projector_sum" \
  --context-file lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean \
  --formalize --line 350
```

## Relationship to the Codex

The Codex defines the normative distinction between:
- real theorem closure
- honest visible debt
- dishonest certificate-style obfuscation

See:
- `docs/codex/codex.md`

The production evolution system is the enforcement and adaptation machinery for
that doctrine. In short:
- the Codex states the rule
- the skills encode the working methodology
- GEPA mutates the methodology
- RealEvaluator scores it against reality
- ProofSeeker tries to rescue failed cases
- VacuityCritic extends the conscience of the system

## Relationship to the Audit Skills

Two skills currently sit at the center of this loop.

### `audit-proof`
Defines the strict audit persona:
- Lean-owner-side proofs
- no wrapper or certificate substitution
- three-bucket audit discipline
- kernel-checkable output preference

### `closure-debt-proof`
Defines the repair doctrine for `_True` / `_sorryProof` / synonym surfaces:
- remove dishonest proof-shaped fields
- replace them with theorem surfaces or explicit theorem-level debt
- keep debt visible rather than hiding it in structure fields

These two skills are not incidental prompt fragments. They are part of the
actual executed pipeline, especially in the proof-seeking lanes.

## Artifacts and Evidence Surfaces

Primary evidence surfaces for this system are:
- `tools/infra/evolution_worker.py`
- `tools/infra/gepa_evolver.py`
- `tools/infra/gepa_real_eval.py`
- `tools/infra/proof_seeker.py`
- `tools/infra/vacuity_critic.py`
- `tools/infra/evolution-worker.service`
- `docs/GOAL_LOOP_SOP.md`
- `docs/codex/codex.md`
- `skills/audit-proof/SKILL.md`
- `skills/closure-debt-proof/SKILL.md`

Closed theorem owners that now anchor the current audit state:
- `lean/InfoGeometry/Canonical/HodgeKreinDeterminantBridge.lean`
- `lean/InfoGeometry/Canonical/TriFacetEigenspace.lean`
- `lean/InfoGeometry/Canonical/HodgeKreinTriFacet.lean`
- `lean/InfoGeometry/Canonical/HodgeKreinSuperLaplacian.lean`
- `lean/InfoGeometry/Foundations/AxiomaticDependencyGraph.lean`
- `lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean`
- `lean/InfoGeometry/Algebra/SplitQuaternionMatrices.lean`

## Non-Goals / Honesty Notes

This document describes the implemented production lane in the repository. It
should not be read as claiming that every queued task fully closes, or that all
proof debt in the repository is solved automatically.

What is implemented:
- autonomous queue worker
- skill mutation
- grounded evaluation
- proof escalation
- anti-pattern discovery
- archival lineage

What still depends on task-by-task success:
- actual theorem closure in a given Lean file
- elimination of all closure debt
- universal success of every evolved skill variant

That distinction matters. A working evolution system is not the same thing as a
fully solved theorem corpus.
