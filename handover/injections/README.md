# Knowledge Injection Subsystem

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This directory documents the packet-oriented injection workflow used for
research intake and translation.

It is a maintained local guide for this subsystem, not the top-level authority
for the whole repository.

## Current Role

The subsystem stores packet lanes such as:

- `raw/`
- `distilled/`
- `translated/`
- `gated/`
- `accepted/`
- `rejected/`
- `archive/`

Its runtime scripts live mostly under `tools/infra/`.

## Important Rule

Packets and digests are workflow memory. They do not outrank the current code,
Lake scripts, or maintained repo-level docs.

Start repo-wide orientation here instead:

- [../../README.md](../../README.md)
- [../../docs/README.md](../../docs/README.md)
- [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)
