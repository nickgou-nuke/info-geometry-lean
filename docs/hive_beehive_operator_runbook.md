# Hive Beehive Operator Runbook

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: exact operator start order for the current beehive architecture
> Authority: operational guidance only; Lean, Lake, and audit gates remain the truth authorities.

This runbook turns the beehive architecture into an execution order.
It assumes the repository is already cloned and the docs in this directory have been read.

## 1. Prerequisites

Before starting the swarm, make sure these are true:

- Arango env file exists at `configs/local/hive_arango.env` or via `HIVE_ARANGO_ENV_FILE`
- the Arango password is not the placeholder `CHANGE_ME`
- the repo virtualenv exists if you want `hive_with_env.sh` to use it
- Lean / Lake / local model services needed by the chosen workers are already running
- the queue database is reachable from the machine running the hive

## 2. Bring up the storage and control plane first

Run these in this order:

1. Initialize the Hive schema

```bash
./tools/infra/hive_with_env.sh init
```

2. Check the Arango/queue health

```bash
./tools/infra/hive_ping.sh
./tools/infra/hive_with_env.sh status
```

3. Optionally seed or inspect queue state

```bash
./tools/infra/hive_with_env.sh queue-stats
./tools/infra/hive_with_env.sh status
```

If the queue is not healthy, stop here.
Do not start workers until the storage layer passes.

## 3. Start the router / dispatcher layer

MotherBee is the deterministic packet router.
It does not expose a built-in continuous flag, so run it under a supervisor or a tiny shell loop.

One-shot dispatch:

```bash
python3 tools/infra/hive_motherbee.py once
```

Continuous loop for local testing:

```bash
while true; do
  python3 tools/infra/hive_motherbee.py once
  sleep 5
done
```

Recommended use:
- start MotherBee after the queue is healthy
- keep it separate from the proof/build/audit workers
- let it append BeeTask envelopes back into the ledger

## 4. Start the swarm workers in narrow lanes

Use one process per lane.
Do not collapse proof, build, audit, and research into one worker.

### 4.1 Proof / tactic lane

Start the main proof bee:

```bash
python3 tools/infra/hive_bee.py --once
```

For continuous operation:

```bash
python3 tools/infra/hive_bee.py --poll-interval 15
```

If you need a different retrieval strategy, override `--retrieval-strategy`.

### 4.2 Swarm proposal / critique / audit lane

Start the multi-role swarm worker:

```bash
python3 tools/infra/hive_swarm.py --once
```

For continuous operation:

```bash
python3 tools/infra/hive_swarm.py --poll-interval 15
```

Use this lane when you want generator → critic → auditor behavior around one queue.

### 4.3 Build truth lane

Start the build worker:

```bash
python3 tools/infra/hive_build_worker.py --once
```

For continuous operation:

```bash
python3 tools/infra/hive_build_worker.py --poll-interval 15
```

This lane should only do `build.verify` work through the locked build wrapper.

### 4.4 Semantic audit lane

Start the audit worker:

```bash
python3 tools/infra/hive_audit_worker.py --once
```

For continuous operation:

```bash
python3 tools/infra/hive_audit_worker.py --poll-interval 15
```

This lane is a gate, not a promotion worker.

### 4.5 Research intake lane

Start the research digest worker:

```bash
python3 tools/infra/research_digest_worker.py --once
```

For continuous operation:

```bash
python3 tools/infra/research_digest_worker.py --poll-interval 30
```

Use this lane to keep intake and theorem truth separate.

## 5. Recommended startup order for an actual swarm

If you want the safest order, start them like this:

1. `./tools/infra/hive_with_env.sh init`
2. `./tools/infra/hive_ping.sh`
3. `python3 tools/infra/hive_motherbee.py once` in a loop or supervised service
4. `python3 tools/infra/hive_bee.py --poll-interval 15`
5. `python3 tools/infra/hive_swarm.py --poll-interval 15`
6. `python3 tools/infra/hive_build_worker.py --poll-interval 15`
7. `python3 tools/infra/hive_audit_worker.py --poll-interval 15`
8. `python3 tools/infra/research_digest_worker.py --poll-interval 30`

Why this order:
- storage first
- router second
- proof and swarm workers after the queue is healthy
- build/audit after proof traffic exists
- research intake last because it is feedstock, not authority

## 6. Enqueueing work

Use the queue tool to create work for the appropriate lane.

Common entrypoints:

```bash
./tools/infra/hive_with_env.sh enqueue-goal --help
./tools/infra/hive_with_env.sh enqueue-build-verify --help
./tools/infra/hive_with_env.sh enqueue-audit --help
./tools/infra/hive_with_env.sh enqueue-promotion --help
```

Typical lane mapping:

- proof tasks: `enqueue-goal`, `enqueue-hybrid-goal`, `enqueue-leansearch-goal`
- build tasks: `enqueue-build-verify`
- audit tasks: `enqueue-audit`
- promotion tasks: `enqueue-promotion`

## 7. Supervision options

Recommended installer for the user units:

```bash
bash ./scripts/install_hive_beehive_systemd_units.sh
```

Use `--no-start` if you want to install and enable without launching the swarm immediately.


Use one of these depending on how long you want the hive to live:

- `tmux` for interactive local supervision
- `systemd --user` for durable background services
- Hermes cron for repeated scheduled passes
- `terminal(background=true, notify_on_complete=true)` for bounded jobs

Suggested division:
- MotherBee: systemd or tmux loop
- proof/build/audit workers: systemd or tmux
- research worker: cron or systemd depending on ingest rate

## 8. Health checks during operation

Check these regularly:

```bash
./tools/infra/hive_ping.sh
./tools/infra/hive_with_env.sh status
./tools/infra/hive_with_env.sh queue-stats
```

If something stalls:
- inspect worker leases
- inspect queue state
- inspect packet lineage
- inspect the latest build packet before blaming the audit lane

## 9. Failure discipline

If a worker fails:

- do not promote from an unverified build packet
- do not treat a proposal packet as truth
- do not let the router become a hidden authority
- do not keep spawning the same failing worker without changing the lane or the model

## 10. Minimal operator mnemonic

The beehive should feel like this:

- queue first
- router second
- proof third
- build fourth
- audit fifth
- research feedstock last
- promotion only after truth gates
