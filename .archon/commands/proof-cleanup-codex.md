---
description: Start the unbounded proof-cleanup heartbeat using the Codex-backed one-cycle workflow.
argument-hint: '[optional scope overrides]'
---

# Proof Cleanup Forever with Codex

**Input**: $ARGUMENTS

---

## Your Mission

Start the repository proof-cleanup heartbeat with Codex as the one-cycle cleanup agent. Let it run continuously until the user interrupts it with Ctrl-C.

**Loop script**: `tools/heartbeat/archon_repo_cleanup_loop.sh`
**Inner workflow**: `proof-sop-cycle-codex`

This command intentionally does **not** use an Archon `loop:` node because loop nodes require `max_iterations`. The Codex cleanup heartbeat is a shell-level life-force loop and stops by Ctrl-C.

---

## Phase 1: LOAD - Check Prerequisites

### 1.1 Confirm Codex CLI

Run:

```bash
command -v codex
```

If missing, report that Codex must be installed with:

```bash
npm install -g @openai/codex
```

### 1.2 Confirm Auth Is Local

Codex authentication must come from local `codex login` or environment variables. Never print or commit Codex tokens.

**PHASE_1_CHECKPOINT:**
- [ ] `codex` binary exists
- [ ] No secrets printed
- [ ] No secrets staged

---

## Phase 2: RUN - Start Codex Heartbeat

Run until Ctrl-C:

```bash
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle-codex \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Do not add bounds unless explicitly requested:

```text
MAX_ITERATIONS
MAX_STALE_ITERATIONS
ARCHON_CYCLE_TIMEOUT_SECONDS
STOP_WHEN_CLEAN=1
```

Optional mathlib/full-repo deterministic gate after each tick:

```bash
POST_TICK_COMMAND='lake build InfoGeometry.Canonical.All'
```

Optional bounded batch mode, only on explicit request:

```bash
MAX_ITERATIONS=5 \
MAX_STALE_ITERATIONS=2 \
ARCHON_CYCLE_TIMEOUT_SECONDS=1800 \
STOP_WHEN_CLEAN=1 \
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle-codex \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

**PHASE_2_CHECKPOINT:**
- [ ] Codex heartbeat started
- [ ] Inner workflow is `proof-sop-cycle-codex`
- [ ] Outer loop is unbounded unless explicitly overridden

---

## Phase 3: REPORT - If Interrupted or Exited

If the command exits, report:

- stop reason or interrupt;
- PID file path `reports/cleanup-loop/archon-repo-cleanup.pid` if still present;
- summary TSV path under `reports/cleanup-loop/<RUN_ID>/summary.tsv`;
- latest before/after heartbeat counts;
- any nonzero Archon or Codex exit codes.

Generated loop logs stay under `reports/cleanup-loop/<RUN_ID>/` and must not be staged.

## Success Criteria

- **CODEX_AVAILABLE**: Codex CLI was found.
- **HEARTBEAT_STARTED**: The Codex cleanup loop is running.
- **UNBOUNDED_BY_DEFAULT**: No iteration/stale/timeout/clean stop was added.
- **SECRETS_LOCAL**: No Codex credentials were printed or committed.
