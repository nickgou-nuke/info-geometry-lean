# BWRAP Troubleshooting

## `bwrap` fails with `RTM_NEWADDR` / `uid_map` permission errors

In restrictive Ubuntu/Debian-like environments, the probe can fail with:

- `loopback: Failed RTM_NEWADDR: Operation not permitted`
- `setting up uid map: Permission denied`

Common reason:
- `kernel.apparmor_restrict_unprivileged_userns=1`

This blocks unprivileged user-namespace operations even for local loopback setup, so
`bwrap` cannot safely create the sandbox.

## Fast diagnostics from `tools/infra/bwrap_preflight.sh`

Run:

```bash
./tools/infra/bwrap_preflight.sh --hint-json
```

Typical output fields:
- `failure_reason`: can be `apparmor_userns`, `uid_map_permission_denied`, or `loopback_restriction`
- `fallback_active`: `true` means sandbox was not used
- `remediation.policy_command`
- `remediation.debug_env`

## Temporary host workaround (test only)

If this is a local machine for testing:

```bash
sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
```

And then re-run:

```bash
BWRAP_EXTRA_ARGS="--share-net" ./tools/infra/bwrap_preflight.sh --hint -- .venv-py312/bin/python -c "print('ok')"
```

## Recommended long-term path

- Keep sandbox policies explicit and allow local networking only where needed by policy.
- Keep `fallback` semantics in `bwrap_preflight.sh`; it preserves portability when
  running under restrictive hosts.
- For CI, treat restricted runners as expected only when their runner class is known.
- Example gate (pseudo):

```bash
info="$(./tools/infra/bwrap_preflight.sh --hint-json)"
status="$(printf '%s' "$info" | tr -d '\\n' )"
# If your CI sets RUNNER_PROFILE=restricted and supports fallback:
if printf '%s' "$status" | grep -q '"sandbox_ready": false' \
  && printf '%s' "$status" | grep -q '"fallback_active": true' \
  && [ "${RUNNER_PROFILE:-}" = "restricted" ]; then
  echo "Runner restriction accepted by policy profile: restricted"
  exit 0
fi
```

(The snippet is intentionally text-only and does not rely on `jq`.)

## Centralized Python sandboxing for large script fleets

For repositories with many Python entrypoints, use a repository-local transparent wrapper instead of editing every script.

1. Source bootstrap to install and enable wrappers in one command:

```bash
source tools/infra/bootstrap_env.sh
```

2. `bootstrap_env` prepends `tools/infra/sandbox-bin` into `PATH` and makes all shims executable.
3. Keep `tools/infra/bwrap_preflight.sh` as the policy oracle.
4. Keep these env flags documented in your environment:
   - `BWRAP_REQUIRE_SANDBOX`
   - `BWRAP_PYTHON_WRAPPER_MODE`
   - `BWRAP_LEAN_WRAPPER_MODE`
   - `BWRAP_LAKE_WRAPPER_MODE`

Set wrappers executable once manually (if needed):

```bash
chmod +x tools/infra/sandbox-bin/python tools/infra/sandbox-bin/python3
chmod +x tools/infra/sandbox-bin/lean tools/infra/sandbox-bin/lean4
```

Example local CI profile:

```bash
export PATH="$PWD/tools/infra/sandbox-bin:$PATH"
export BWRAP_EXTRA_ARGS="--share-net" # optional
python3 -m pytest tests/...
```

The wrappers delegate through:

- `python`/`python3` + `bwrap_preflight.sh`
- `lean`/`lean4` + `bwrap_preflight.sh`
- explicit fallback when supported reasons are detected
- optional strict mode with `BWRAP_REQUIRE_SANDBOX=1`
- optional interpreter overrides:
  - `BWRAP_PYTHON_BIN` (default: `python`)
  - `BWRAP_LEAN_BIN` (default: `lean`, or `lean4` for `lean4` wrapper)
- optional mode flags:
  - `BWRAP_PYTHON_WRAPPER_MODE` (`sandbox`, `fallback-ok`, `off`)
  - `BWRAP_LEAN_WRAPPER_MODE` (`sandbox`, `fallback-ok`, `off`)
  - `BWRAP_LAKE_WRAPPER_MODE` (`sandbox`, `fallback-ok`, `off`)

This gives “single-point” infrastructure behavior for many scripts.

Lean-focused examples:

```bash
export PATH="$PWD/tools/infra/sandbox-bin:$PATH"
export BWRAP_LEAN_WRAPPER_MODE=fallback-ok
export BWRAP_REQUIRE_SANDBOX=1  # optional strict mode
lake build
```

Bootstrap usage in CI:

```bash
source tools/infra/bootstrap_env.sh --ci
```

`--ci` additionally exports wrapper mode and flags to `$GITHUB_ENV` and adds shim directory to `$GITHUB_PATH`.
