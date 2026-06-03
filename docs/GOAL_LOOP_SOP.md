# Goal Loop SOP — Autonomous Closure Loop

> Status: `production — 2026-06-03`
> Scope: self-evolving autonomous pipeline for closing certificate debt.

## Architecture

The goal loop is implemented as a systemd daemon (`evolution-worker.service`)
that polls the ArangoDB `skill-evolution` queue every 5 seconds. Each task
triggers the full pipeline:

```
Queue → GEPA/DSPy → RealEvaluator → 3-Stage Prover → VacuityCritic → Archive
```

The pipeline is not a bounded state machine — it is a continuous self-improving
loop. Each generation improves the skill. Each failure expands the detection
dictionary. Each success is archived with fitness score.

## Agents

| Agent | Module | Function |
|---|---|---|
| GEPA/DSPy | `gepa_evolver.py` | Mutates skill via Pareto genetic search |
| RealEvaluator | `gepa_real_eval.py` | Tests skill against real `_True` fields |
| Pi Coding Agent | `@earendil-works/pi` | Proof generation + compile → fix → repeat |
| ChatGPT Auditor | `run_audit.py` | Browser CDP → full file context → formatted code extraction |
| Vacuity Critic | `vacuity_critic.py` | Discovers new obfuscation pattern synonyms |
| Proof Seeker | `proof_seeker.py` | arXiv/Mathlib search on failure |
focused on a declared task until the task is done, blocked, paused, cleared, or
preempted by the user.

## Invariants

1. A standing goal is set explicitly with nonempty text.
2. Goal state is persisted per session under `artifacts/goal-loop/`.
3. Continuation prompts are ordinary user-message text.
4. The system prompt is never mutated.
5. The toolset is never swapped.
6. User messages preempt continuation and should pause the loop for that turn.
7. The judge is the only arbiter of `done`.
8. Judge output must be strict JSON:

```json
{"done": true, "reason": "..."}
```

or

```json
{"done": false, "reason": "..."}
```

9. Judge parse failures fail open as `continue`.
10. Three consecutive judge parse failures auto-pause the loop and require a
    stricter judge route.
11. Turn-budget exhaustion auto-pauses the loop.
12. `/subgoal`-style criteria are first-class and included in both continuation
    and judge context.

## CLI

Set a goal:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" set \
  "Native AFP/JNF debt closure without sorry/admit/axiom"
```

Add a subgoal:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" subgoal \
  "Build the touched Lean modules"
```

Render the next continuation prompt:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" continuation
```

Apply a judge verdict:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" judge \
  --json '{"done": false, "reason": "Spectral-radius strict case remains open"}'
```

Pause, resume, clear, and inspect:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" pause --reason "user preempted"
python3 tools/infra/goal_loop.py --session "$SESSION_ID" resume
python3 tools/infra/goal_loop.py --session "$SESSION_ID" clear
python3 tools/infra/goal_loop.py --session "$SESSION_ID" status
```

## Closure-Debt Use

For native Lean closure work, the standing goal should name the exact debt lane
and forbid witness replacement, for example:

```text
Native AFP/JNF debt closure: replace packet/witness leftovers with
kernel-checked Lean proofs, step by step, without sorry/admit/axiom.
```

The goal loop may keep an agent working. It may not promote a theorem. Promotion
still requires the constructive closure mandate: a kernel-checked Lean proof or
an imported mathlib theorem.
