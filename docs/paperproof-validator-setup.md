# Paperproof + Paperproof-Validator Setup

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## 1) Project toolchain and compatibility

- `lean-toolchain`: `leanprover/lean4:v4.28.0`
- `Paper-Proof/paperproof` compatibility table (`VERSIONS.md`) supports Lean `v4.27.0` through `v4.29.0` with `rev = "main"` for the library and VSCode extension `v2.7.0`.

## 2) Exact `lakefile.lean` dependency block

```toml
[[require]]
name = "Paperproof"
git = "https://github.com/Paper-Proof/paperproof.git"
rev = "main"
subDir = "lean"
```

## 3) Installed skill

- `paperproof-validator` is already installed for Codex at:
  - `/home/goutev/.codex/skills/paperproof-validator`

## 4) Common commands to use in this repo

- Update dependency:
  - `cd /home/goutev/repos/info-geometry-lean-fusion`
  - `lake update Paperproof` (or `lake update`)
- Check installed skill:
  - `npx --yes skillfish list --json`
- Skill entrypoint (agent usage):
  - `npx --yes skillfish add plurigrid/asi paperproof-validator`
- Use in Lean file:
  - `import Paperproof`
- In VS Code Paperproof commands:
  - `Paperproof: Open Paperproof Panel`
  - `Paperproof: Show Current Theorem`
  - `Paperproof: Export Proof as Image`
  - `Paperproof: Settings`
