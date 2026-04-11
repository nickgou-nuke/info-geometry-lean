# DAG Troubleshooting

Use this page when the managed DAG lane is stale, blocked, or inconsistent.

## Build Lock Is Held

Check status first:

```bash
lake script run dagStatus
```

If another active build is running, wait for it to finish and then rerun:

```bash
lake script run dagAll
```

If the lock metadata is stale but no real build is active, clear it using the repo's normal locked-build cleanup path rather than deleting files manually.

## Authoritative Artifacts Are Missing Or Stale

Run:

```bash
lake script run dagRefresh
```

Then regenerate reports and re-diagnose:

```bash
lake script run dagReports
lake script run dagDoctor
```

Or do the full managed repair:

```bash
lake script run dagAll
```

## Reports Are Missing Or Stale

Run:

```bash
lake script run dagReports
```

Then confirm:

```bash
lake script run dagDoctor
```

## The Indexer Or Managed Refresh Failed

First get the exact diagnosis:

```bash
lake script run dagDoctor
```

Common causes:
- build target does not compile
- stale or partial artifacts
- local environment drift
- interrupted report generation

If the underlying Lean build is the issue, fix the build first and rerun:

```bash
lake script run dagAll
```

## Blueprint Or Depth Tags Look Wrong

Refresh the tag surfaces first, then rerun the managed lane if needed.

Typical repair commands:

```bash
python3 tools/infra/refresh_blueprint_tags.py
lake script run dagAll
```

## I Only Changed Lean Files

Do not run the whole DAG lane by default. Start with:

```bash
lake script run changedVerify
```

Add `--dry-run` if you only want the planned commands:

```bash
lake script run changedVerify -- --dry-run
```

## I Need Local Proof-State Or Frontier Work

Use the proof/frontier tools, not DAG refresh:

```bash
lake script run proofSession
lake script run proofPrint -- InfoGeometry.Canonical.SomeModule
lake script run semanticSnapshot
```

## Repair Order

Use this order unless you have a specific reason not to:

1. `lake script run dagDoctor`
2. `lake script run dagAll`
3. `lake script run changedVerify` for changed Lean work
