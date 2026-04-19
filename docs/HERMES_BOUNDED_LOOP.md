# Hermes Bounded Loop

This document defines the first safe recurring loop for the local theorem
factory.

The loop is intentionally bounded. It is not a raw infinite shell loop.

## Behavior

Each trigger performs one cycle:

1. read Hermes research packets from `quarantine/hermes_memory/research_packets`
2. select one `draft` packet
3. ask the planner lane for a routing decision
4. write artifacts under `artifacts/hermes_loop/runs`
5. update `artifacts/hermes_loop/state.json`
6. stop

The runner does not:

- edit Lean files
- call `Codex CLI`
- run `lake`
- promote canonical content
- claim theorem closure

## Runner

```bash
cd /home/goutev/repos/info-geometry-lean
python3 tools/infra/hermes_bounded_runner.py
```

Dry-run mode:

```bash
python3 tools/infra/hermes_bounded_runner.py --dry-run
```

## Planner Lane

The default planner lane is local Nemotron:

- base URL: `http://127.0.0.1:30000/v1`
- model: `Nemotron-3-Nano-30B-A3B-UD-Q8_K_XL.gguf`

Environment overrides:

- `HERMES_LOOP_BASE_URL`
- `HERMES_LOOP_MODEL`
- `HERMES_LOOP_API_KEY`
- `HERMES_LOOP_TIMEOUT`
- `HERMES_LOOP_MAX_TOKENS`

## Systemd User Timer

The host-level timer is:

- `hermes-info-geometry-loop.timer`

It calls:

- `hermes-info-geometry-loop.service`

The default schedule is one bounded planning cycle every 30 minutes.

Current host state:

- timer is installed in `/home/goutev/.config/systemd/user/hermes-info-geometry-loop.timer`
- service is installed in `/home/goutev/.config/systemd/user/hermes-info-geometry-loop.service`
- timer is enabled
- service uses `flock` to avoid overlapping cycles
- Nemotron serving context is currently `32768`
- Hermes CLI context override is currently `64000` to pass Hermes' startup
  guard
- the bounded runner does not depend on Hermes interactive session history and
  uses compact direct planner calls

Useful commands:

```bash
export XDG_RUNTIME_DIR=/run/user/1000
systemctl --user status hermes-info-geometry-loop.timer
systemctl --user status hermes-info-geometry-loop.service
journalctl --user -u hermes-info-geometry-loop.service -f
```

Run one cycle manually:

```bash
systemctl --user start hermes-info-geometry-loop.service
```

## Promotion Boundary

This loop is allowed to plan forever.

It is not allowed to mutate forever.

Execution must be introduced through a separate explicit gate that consumes
planner artifacts and decides whether a `Codex CLI` action is justified.
