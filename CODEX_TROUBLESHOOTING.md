# Codex CLI Troubleshooting

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for local operator troubleshooting, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This file tracks local Codex-side issues that can block repo work even when the
repository itself is fine.

## First Rule

If Codex behavior looks wrong, separate:

- repo failure
- local CLI/runtime failure
- remote API/config failure

Do not assume a Lean or toolchain bug until the CLI layer has been checked.

## Practical Checks

1. confirm the repo commands still work in a plain shell
2. compare with `lake script run changedVerify` or `dagDoctor`
3. inspect local config or prompt-compaction issues only after shell commands
   reproduce correctly

## Current Repo Anchors

When in doubt, test one of these:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

If these behave correctly in the shell, the repo is usually fine and the issue
is higher in the Codex/CLI stack.
