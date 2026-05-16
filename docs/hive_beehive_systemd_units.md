# Hive Beehive systemd user units

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: user-level service templates for running the beehive continuously
> Authority: operational guidance only; the runtime scripts, queue state, Lean kernel, and audit gates remain authoritative.

This directory now contains the service templates that implement the beehive runbook.
A helper installer script lives at `scripts/install_hive_beehive_systemd_units.sh`.
The units are designed for `systemd --user` and use a single target to start the swarm.

## Files

- `systemd/user/hive-beehive.target`
- `systemd/user/hive-motherbee.service`
- `systemd/user/hive-bee@.service`
- `systemd/user/hive-swarm@.service`
- `systemd/user/hive-build@.service`
- `systemd/user/hive-audit@.service`
- `systemd/user/hive-research@.service`

## Recommended enable/start sequence

1. Install or copy the unit files into the user systemd directory.
2. Reload the user daemon:

```bash
systemctl --user daemon-reload
```

3. Start the whole swarm:

```bash
systemctl --user enable --now hive-beehive.target
```

4. Check status:

```bash
systemctl --user status hive-beehive.target
systemctl --user status hive-motherbee.service
systemctl --user status hive-bee@default.service
systemctl --user status hive-swarm@default.service
systemctl --user status hive-build@default.service
systemctl --user status hive-audit@default.service
systemctl --user status hive-research@default.service
```

5. Watch logs:

```bash
journalctl --user -u hive-beehive.target -f
journalctl --user -u hive-bee@default.service -f
```

## Why the template layout looks like this

- `hive-beehive.target` is the swarm entrypoint.
- `hive-motherbee.service` is the deterministic router / dispatcher.
- `hive-bee@.service` is the proof lane.
- `hive-swarm@.service` is the proposal / critique / auditor lane.
- `hive-build@.service` is the build truth lane.
- `hive-audit@.service` is the semantic audit gate.
- `hive-research@.service` is the intake / digest lane.

## Notes

- The units are intentionally narrow.
- They do not merge proof, build, audit, and ingestion into one process.
- They rely on the repo scripts for queue logic and provider routing.
- If you need more than one worker in a lane, start another instance with a different suffix, for example `hive-bee@2.service`.
- If you need machine-specific overrides, use a drop-in at `~/.config/systemd/user/<unit>.d/override.conf`.

## Operational caveat

The units assume the local environment is already prepared:

- the Arango env file is reachable
- the queue database is healthy
- the repository working tree is available at `/home/goutev/repos/info-geometry-lean`
- the chosen provider/model path is usable by the worker script

If any of those are not true, fix the underlying lane first and do not rely on restart loops to recover truth.
