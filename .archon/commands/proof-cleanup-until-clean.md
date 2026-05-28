# proof-cleanup-until-clean

Run a bounded Archon proof-cleanup supervisor loop.

```bash
MAX_ITERATIONS=25 \
MAX_STALE_ITERATIONS=3 \
ARCHON_CYCLE_TIMEOUT_SECONDS=1800 \
SCOPE=lean/InfoGeometry/Canonical \
WORKFLOW=proof-sop-cycle \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

The loop repeatedly runs the existing one-cycle workflow:

```bash
archon workflow run proof-sop-cycle --cwd "$ROOT" --no-worktree
```

It stops when one of these happens:

1. heartbeat score reaches zero;
2. progress stalls for `MAX_STALE_ITERATIONS` iterations;
3. an inner cycle times out or exits nonzero and no later progress is made;
4. `MAX_ITERATIONS` is reached.

The heartbeat score is:

```text
sorry + proxy_field + prop_socket + reexport_proxy
```

Logs are written under:

```text
reports/cleanup-loop/<RUN_ID>/
```

Do not stage generated loop logs or Ulam JSON artifacts unless explicitly asked.
