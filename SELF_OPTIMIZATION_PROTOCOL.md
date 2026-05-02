# Self-Optimization Protocol

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This repository allows guarded self-improvement of its code and tooling. It
does not allow graph-driven free play detached from current source.

## Allowed Loop

1. inspect the current code
2. make one narrow change
3. verify the changed file or module
4. rerun managed repo checks if the change widens in scope
5. keep the change only if the code surface is clearer or more correct

## Guardrails

- no theorem claim without Lean proof
- no graph-only rewrite of live owner files
- no trusting stale artifacts as current evidence
- no broad cleanup without preserving existing user changes

## Verification Surface

Use:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

Use `lake script run dagAll` only when you actually need a full structural
refresh.
