# Bridge Thinness Index

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a report snapshot, not as current policy.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This file is a checked-in thinness report snapshot.

## Use It For

- historical review of bridge-facing theorem surfaces
- comparing older debt audits with current code

## Do Not Use It For

- deciding current theorem truth
- deciding current repository status without regeneration

For current structural checks, prefer:

```bash
lake script run dagDoctor
lake script run dagAll
```
