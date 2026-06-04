# Autonomous Self-Improving Proof Chain — Repo-Native SOP

## Purpose

This SOP defines the standard operating procedure for invoking the autonomous,
self-improving proof chain in `info-geometry-lean`.

The chain is a proposal-and-verification system for open Lean theorem debts. It
may use auxiliary agents, browser audits, queue workers, and literature lookup,
but none of those are proof authority.

Authoritative closure in this repo means:
- the target theorem is stated honestly;
- the proof is native Lean, or the remaining gap is stated explicitly;
- `lake env lean <file>` succeeds;
- the narrow locked build succeeds where applicable;
- the result is classified honestly as BUCKET 1, 2, or 3.

Implementation surfaces used by this SOP:
- `tools/infra/seed_goals_from_sorries.py`
- `tools/infra/evolution_worker.py`
- `tools/infra/gepa_evolver.py`
- `tools/infra/gepa_real_eval.py`
- `tools/infra/proof_seeker.py`
- `tools/infra/chatgpt_browser_harness_driver.py`
- `tools/infra/hermes_self_evolver.py`
- `tools/infra/skill_mutator.py`
- `tools/infra/evolution_evaluator.py`
- `tools/infra/vacuity_critic.py`
- `tools/infra/mission_loop.py`

## Authority Policy

Always keep this ordering explicit:

1. Lean kernel / current repo source
2. `lake env lean` / locked build artifacts
3. exact owner/translator theorem surfaces already in repo
4. proposal engines (Hermes, GEPA, Pi, browser audit, literature search)
5. prose notes / research dumps / external chat output

The chain can propose. It cannot promote by itself.

## Repo-Specific Safety Rules

- Do not treat browser/ChatGPT output as theorem authority.
- Do not treat Arango/DAG overlays as proof authority.
- Do not remove debt markers unless a native Lean proof term closes that debt.
- Do not replace debt with `_True`, `_holds`, `_certificate`, wrapper fields, or
  other nominal closure surfaces.
- Prefer the smallest truthful theorem target over a grand synthesis claim.
- For `info-geometry-lean`, do not default-route to Gemini/Google-backed lanes.
  If an operator explicitly requests such a lane, treat it as a non-authoritative
  sidecar only.

## Prerequisites

Required runtime/services:

- Chromium/Chrome with remote debugging if browser audit is enabled:
  `chromium --remote-debugging-port=9222 &`
- ChatGPT logged in at `chatgpt.com` if browser audit is enabled
- ArangoDB running on `http://127.0.0.1:8530` if the queue/graph worker is used
- required API keys in `~/.hermes/.env`
- `pi` coding agent on PATH if Stage 1 coding-agent escalation is enabled
- `browser-harness` on PATH if Stage 0 browser audit is enabled

Required repo posture before launch:

- clean understanding of the exact theorem debt(s) to target
- no ambiguity about target file/module/line
- no concurrent unrelated rewrite loop on the same file
- build commands known in advance for the target module

## Debt Intake Gate

Only enqueue debts that satisfy all of the following:

- exact target theorem name is known;
- exact file path is known;
- exact line or local theorem neighborhood is known;
- claim is Lean-sized and local enough to compile-check quickly;
- claim is honestly classifiable as current BUCKET 3 debt.

Do not enqueue:
- large prose blobs;
- broad research themes;
- repeated text dumps;
- “prove the whole architecture” tasks;
- claims whose statement is still mathematically unstable.

## BUCKET Definitions

Use these definitions throughout the chain.

### BUCKET 1 — Closed finite/native theorems
A theorem belongs here only if it is already native-closed by the kernel in its
honest stated scope.

### BUCKET 2 — Conditional theorems from explicit witnesses
A theorem belongs here if it is proved from explicit stated hypotheses/witnesses,
but still depends on those witnesses rather than a stronger owner-side closure.

### BUCKET 3 — Open closure debt
A theorem belongs here if any of the following remain true:
- no native Lean proof yet;
- statement still relies on external certificate/witness scaffolding;
- compile is green only because of `sorry` or placeholder debt;
- analytic/topological claims outrun current repo authority.

## Phase 1: Seed the Debt

Identify exact BUCKET 3 theorems and enqueue them.

Pattern:

```bash
python3 -c "
from tools.infra.hive_arango_queue import enqueue_goal, aql
from tools.infra.arango_env import *
from pathlib import Path
import hashlib

load_repo_arango_env(Path.cwd())
ep = arango_endpoint()
db = arango_database('hive_live')
usr = arango_username()
pwd = arango_password('alexandria_root')

# Clear only the intended queue if you really want a fresh run.
aql(ep, db, usr, pwd,
    'FOR t IN hive_tasks FILTER t.queue_name == \"proof-search\" REMOVE t IN hive_tasks')

debts = [
    ('lean/InfoGeometry/Canonical/BerezinianTrace.lean', 57, 'det_exp_eq_exp_tr'),
    ('lean/InfoGeometry/Canonical/BerezinianTrace.lean', 65, 'ber_exp_eq_exp_str'),
]

for file, line, name in debts:
    target = f'Prove `{name}` in {file}:{line}'
    gh = hashlib.sha256(target.encode()).hexdigest()[:24]
    enqueue_goal(
        ep, db, usr, pwd,
        queue_name='proof-search',
        goal_hash_shape=gh,
        canonical_shape=gh,
        target_pretty=target,
        module=file.replace('.lean', '').replace('/', '.'),
        goal_index=line,
        priority=1.0,
        task_kind='proof.search'
    )
    print(f'Seeded: {name}')
"
```

Operator checklist before seeding:
- confirm theorem names are exact;
- confirm files still match current repo state;
- confirm these are real debts, not already-closed theorems;
- confirm no broader queue items are accidentally being reused.

## Phase 2: Clear Stale State

Before launching the autonomous chain:

```bash
rm -f /tmp/chatgpt_audit_tab_ready
> quarantine/hermes_skills/evolved/.eval_cache.jsonl
```

Purpose:
- force a fresh browser tab on first audit call;
- clear stale evaluation cache;
- reduce contamination from earlier runs.

## Phase 3: Run the Autonomous Chain

Example invocation:

```bash
python3 tools/infra/gepa_evolver.py \
  --skill audit-proof \
  --generations 3 \
  --real-eval \
  --real-eval-tasks 2
```

Interpretation:
- the skill is mutated;
- real theorem tasks are attempted;
- evaluation is grounded in actual compile behavior;
- files must be restored after evaluation unless deliberately promoted later.

## Per-Generation Execution Model

For each generation:

1. GEPA/DSPy mutates the proof/audit skill.
2. RealEvaluator runs Hermes on the target theorem neighborhood.
3. Hermes attempts local proof repair or theorem closure.
4. The target file is compile-checked with `lake env lean <file>`.
5. If configured, a narrow locked module build is run.
6. The result is scored.
7. The original file is restored after evaluation.
8. Lineage and fitness metadata are archived.

## Scoring Rules

Minimum honest scoring policy:

- score `0.0` if:
  - `sorry` remains in the targeted closure path, or
  - compilation fails, or
  - the statement was weakened without explicit operator approval, or
  - fake closure wrappers were introduced;
- score `1.0` only if:
  - the target debt is actually closed in the intended scope, and
  - the target file compiles, and
  - no forbidden placeholder/certificate pattern was introduced.

Recommended stricter local interpretation:
- do not treat “file compiles but debt moved elsewhere” as success;
- do not treat “proof replaced by witness packet” as success;
- do not treat “comment rewritten to sound stronger” as success.

## Escalation Chain on Failure

When the direct local proof attempt fails, escalate in this order.

### Stage 0: Browser Audit Sidecar

Browser/CDP audit may:
- send full file context to `chatgpt.com`;
- reuse the same tab across calls;
- review large research notes;
- generate an audit map or proof sketch;
- save candidate code and compile-check it;
- retry on compile error up to the configured limit.

Hard rule:
- treat all browser output as proposal-only.

The browser harness lives in `tools/infra/chatgpt_browser_harness_driver.py`.

### Stage 1: Pi / Coding-Agent Sidecar

The coding agent may:
- consume the audit map or proof sketch;
- generate Lean code;
- run write -> compile -> error -> fix loops;
- iterate up to the configured limit.

Hard rule:
- generated code is not success until the repo’s Lean/build gates pass.

The direct coding lane is owned by `tools/infra/proof_seeker.py`.

### Stage 2: Literature / arXiv Sidecar

Literature search may:
- supply mathematical context;
- suggest known identities or decompositions;
- help refine theorem statements.

Hard rule:
- literature context does not promote theorem closure.

## Verification Gates

Every proposed patch must pass the following gates in order.

### Gate A — Exact local file check

```bash
lake env lean path/to/File.lean
```

### Gate B — Narrow locked module build

Use the repo’s locked wrapper where appropriate:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock Module.Name
```

### Gate C — Honest debt classification

After compile success, classify the result explicitly:
- moved to BUCKET 1;
- moved to BUCKET 2;
- remains BUCKET 3.

No theorem is promoted solely because Gate A passed.

## Vacuity Critic / Self-Improvement Step

Failed tasks should be mined for anti-patterns such as:
- wrapper-based fake closure;
- statement drift;
- witness laundering;
- build-green but theorem-open edits;
- comment-level inflation;
- broad unsupported topology/physics claims.

The skill may update its anti-pattern dictionary, but those updates are process
improvements, not mathematical closure.

## Archive and Lineage

After each generation:
- save the evolved skill;
- save the fitness score;
- save a lineage manifest;
- record enough metadata to reproduce the run.

Typical inspection path:

```bash
cat quarantine/hermes_skills/archive/audit-proof/manifest.jsonl | jq .
```

## Monitoring

Examples:

```bash
tail -f /tmp/claude-*/tasks/*.output
```

or, if supervised by systemd:

```bash
journalctl -u evolution-worker -f
```

Monitor for:
- queue pollution from old tasks;
- repeated compile-fail loops with no change in proof shape;
- mutation drift toward wrappers/certificates;
- accidental edits outside the target theorem neighborhood.

## Result Retrieval

After the run:

```bash
git diff --stat
lake build InfoGeometry.Canonical.BerezinianTrace
```

Then manually inspect:
- exact theorem statement;
- proof body;
- whether debt truly closed or merely moved;
- whether the result belongs in BUCKET 1, 2, or 3.

## Promotion Checklist

Promote a result only if all are true:
- theorem statement remained honest;
- no forbidden placeholder/wrapper/certificate surface was introduced;
- target file compiles;
- narrow locked build passes;
- result is correctly bucketed;
- the patch improves actual native closure debt.

## Quick Single-Task Test

Example browser-audit smoke test:

```bash
browser-harness -c "exec(open('tmp/browser-harness/run_audit.py').read()); run_audit_and_save('lean/InfoGeometry/Canonical/BerezinianTrace.lean', open('lean/InfoGeometry/Canonical/BerezinianTrace.lean').read(), 57, '.')"
```

Interpret this as a sidecar test only, not a promotion event.

## Emergency Recovery

Reset state:

```bash
rm -f /tmp/chatgpt_audit_tab_ready
> quarantine/hermes_skills/evolved/.eval_cache.jsonl
```

Restore touched files:

```bash
git checkout -- lean/InfoGeometry/Canonical/BerezinianTrace.lean
```

If the queue was polluted, clear/reseed only after re-validating the target list.

## Minimal Operator Summary

1. Choose exact BUCKET 3 theorem debts.
2. Seed only those debts.
3. Clear stale browser/eval state.
4. Run the evolver.
5. Let local proof repair try first.
6. Use browser/coding/literature stages only as proposal sidecars.
7. Compile-check every attempt.
8. Run the narrow locked build.
9. Re-classify the result honestly.
10. Promote only native closure, not persuasive output.
