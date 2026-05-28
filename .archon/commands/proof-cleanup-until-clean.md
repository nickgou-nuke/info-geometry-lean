# proof-cleanup-forever

Run the Archon proof-cleanup heartbeat continuously. The workflow uses an AI starter node rather than a deterministic bash node because Archon bash nodes require a positive timeout; the heartbeat itself is intentionally unbounded and is stopped by Ctrl-C.

```bash
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Default behavior is intentionally unbounded:

```text
MAX_ITERATIONS=0                  # no iteration limit
MAX_STALE_ITERATIONS=0            # no stale-progress stop
ARCHON_CYCLE_TIMEOUT_SECONDS=0    # no per-cycle timeout wrapper
STOP_WHEN_CLEAN=0                 # continue even if the current score is clean
```

Stop it with Ctrl-C.

Optional bounded batch mode is still available when explicitly requested:

```bash
MAX_ITERATIONS=25 \
MAX_STALE_ITERATIONS=3 \
ARCHON_CYCLE_TIMEOUT_SECONDS=1800 \
STOP_WHEN_CLEAN=1 \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

The loop repeatedly runs the existing one-cycle workflow:

```bash
archon workflow run proof-sop-cycle --cwd "$ROOT" --no-worktree
```

The heartbeat score is:

```text
sorry + proxy_field + prop_socket + reexport_proxy
```

Logs are written under:

```text
reports/cleanup-loop/<RUN_ID>/
```

Do not stage generated loop logs or Ulam JSON artifacts unless explicitly asked.
