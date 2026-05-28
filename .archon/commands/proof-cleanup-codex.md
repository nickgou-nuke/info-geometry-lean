# proof-cleanup-codex

Run the unbounded proof-cleanup heartbeat with the Codex CLI assistant.

Prerequisites:

```bash
command -v codex
codex login
```

Archon config owns the binary path and model under `assistants.codex`.
No Codex tokens should be committed; use local Codex auth or environment variables.

Run until Ctrl-C:

```bash
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle-codex \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Optional bounded batch mode:

```bash
MAX_ITERATIONS=5 \
MAX_STALE_ITERATIONS=2 \
ARCHON_CYCLE_TIMEOUT_SECONDS=1800 \
STOP_WHEN_CLEAN=1 \
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle-codex \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Generated loop logs stay under `reports/cleanup-loop/<RUN_ID>/` and should not be staged.
