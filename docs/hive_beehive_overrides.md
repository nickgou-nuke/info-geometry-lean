# Hive Beehive Overrides and Per-Lane Examples

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: machine-local override examples for the Hive beehive systemd units
> Authority: these are operational examples only; the queue, model routing, and Lean proofs remain the source of truth.

The base units live in `systemd/user/` and are installed into `~/.config/systemd/user/` by:

```bash
bash ./scripts/install_hive_beehive_systemd_units.sh
```

Use systemd drop-ins when one machine or one lane needs a different model, queue file, or environment.

## 1. Per-unit drop-in layout

Example drop-in paths:

- `~/.config/systemd/user/hive-motherbee.service.d/override.conf`
- `~/.config/systemd/user/hive-bee@default.service.d/override.conf`
- `~/.config/systemd/user/hive-swarm@default.service.d/override.conf`
- `~/.config/systemd/user/hive-build@default.service.d/override.conf`
- `~/.config/systemd/user/hive-audit@default.service.d/override.conf`
- `~/.config/systemd/user/hive-research@default.service.d/override.conf`

Reload after changes:

```bash
systemctl --user daemon-reload
systemctl --user restart hive-beehive.target
```

## 2. Example: route the proof lane to a different local model

If one proof lane should use a different resident model endpoint, add a drop-in like:

```ini
[Service]
Environment=HIVE_MODEL_PROVIDER=openrouter
Environment=HIVE_MODEL_NAME=openrouter/free
Environment=HIVE_MODEL_FALLBACK=gemini-3-flash-preview
```

That keeps the lane isolated without changing the global beehive target.

## 3. Example: give the build lane an explicit Lean env file

```ini
[Service]
EnvironmentFile=
EnvironmentFile=-/home/goutev/.config/info-geometry-lean/lean-build.env
Environment=LEAN_TOOLCHAIN=leanprover/lean4:v4.17.0
```

Use this when a build worker needs a stricter or older toolchain than the rest of the swarm.

## 4. Example: make MotherBee point at a different queue file

```ini
[Service]
Environment=HIVE_QUEUE_FILE=/home/goutev/.config/info-geometry-lean/hive-queue.jsonl
Environment=HIVE_LEASE_TTL=120
```

This is useful for machine-local experiments or split-brain avoidance while testing.

## 5. Example: add local logging tweaks

```ini
[Service]
Environment=PYTHONUNBUFFERED=1
Environment=HERMES_LOG_LEVEL=info
StandardOutput=journal
StandardError=journal
```

## 6. When to use overrides

Use a drop-in when:

- only one host differs
- only one lane differs
- you need a model/provider fallback change
- you want to test a local queue or lease setting

Do not use a drop-in to paper over a broken architecture.
If the same workaround appears on multiple machines, move it into the base unit or the installer script.

## 7. Recommended restart sequence after editing overrides

```bash
systemctl --user daemon-reload
systemctl --user restart hive-motherbee.service
systemctl --user restart hive-bee@default.service
systemctl --user restart hive-swarm@default.service
systemctl --user restart hive-build@default.service
systemctl --user restart hive-audit@default.service
systemctl --user restart hive-research@default.service
```

## 8. Uninstall helper

If you want to remove the installed user units, use:

```bash
bash ./scripts/uninstall_hive_beehive_systemd_units.sh
```

Add `--dry-run` first if you want to inspect what will be removed.
