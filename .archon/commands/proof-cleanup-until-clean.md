---
description: Start the unbounded proof-cleanup heartbeat; runs until the user stops it with Ctrl-C.
argument-hint: '[optional scope/workflow overrides]'
---

# Proof Cleanup Forever

**Input**: $ARGUMENTS

---

## Your Mission

Start the repository proof-cleanup heartbeat from the live checkout and let it run continuously until the user interrupts it with Ctrl-C.

**Loop script**: `tools/heartbeat/archon_repo_cleanup_loop.sh`

The workflow uses an AI starter node rather than a deterministic Archon `bash:` node because Archon bash nodes require a positive timeout. It also intentionally does **not** use an Archon `loop:` node: Archon loop nodes require `max_iterations`, which is the wrong primitive for this life-force heartbeat. The heartbeat itself is intentionally unbounded and lives in the shell process until Ctrl-C.

---

## Phase 1: LOAD - Confirm Context

### 1.1 Confirm Repository Root

Run from the current repo root. Do not create a worktree for this command.

### 1.2 Confirm Intentional Infinity

Use the default unbounded settings:

```text
MAX_ITERATIONS=0                  # no iteration limit
MAX_STALE_ITERATIONS=0            # no stale-progress stop
ARCHON_CYCLE_TIMEOUT_SECONDS=0    # no per-cycle timeout wrapper
STOP_WHEN_CLEAN=0                 # continue even if clean
INTERVAL_SECONDS=0                # no artificial sleep between ticks
POST_TICK_COMMAND=''              # optional deterministic mathlib/full-repo gate
```

**PHASE_1_CHECKPOINT:**
- [ ] Running in the repository root
- [ ] No artificial loop bound added
- [ ] User can stop with Ctrl-C

---

## Phase 2: RUN - Start the Heartbeat

Run exactly:

```bash
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Do not add these unless the user explicitly requested bounded batch mode:

```text
MAX_ITERATIONS
MAX_STALE_ITERATIONS
ARCHON_CYCLE_TIMEOUT_SECONDS
STOP_WHEN_CLEAN=1
```

**PHASE_2_CHECKPOINT:**
- [ ] Heartbeat script started
- [ ] Inner workflow remains `proof-purification-pipeline` unless overridden by environment
- [ ] Logs are written under `reports/cleanup-loop/<RUN_ID>/`

---

## Phase 3: REPORT - If Interrupted or Exited

If the command exits, report:

- stop reason or interrupt;
- PID file path `reports/cleanup-loop/archon-repo-cleanup.pid` if still present;
- summary TSV path under `reports/cleanup-loop/<RUN_ID>/summary.tsv`;
- latest before/after heartbeat counts;
- any nonzero Archon exit codes.

Do not stage generated loop logs, reports, or Ulam JSON artifacts.

## Success Criteria

- **HEARTBEAT_STARTED**: The cleanup loop is running.
- **UNBOUNDED_BY_DEFAULT**: No iteration/stale/timeout/clean stop was added.
- **USER_INTERRUPTIBLE**: Ctrl-C remains the stopping mechanism.
- **ARTIFACTS_UNSTAGED**: Generated logs/reports are not staged.
