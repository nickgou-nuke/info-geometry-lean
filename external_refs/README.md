# External References

This directory stores upstream repositories and source mirrors used for proof
mining, literature transfer, symbolic witnesses, or external theorem-provider
context.

Lean proof authority remains in `lean/InfoGeometry`. Files in `external_refs/`
are evidence and navigation context, not owner proofs.

## Current Audit

See:

```text
docs/EXTERNAL_REPOSITORY_INVENTORY.md
```

for the comparison against:

```text
/media/goutev/SP DS72/auto/external
```

## Placement Rules

Use `external_refs/<repo-name>/` for full upstream checkouts or source mirrors.

Use `external/` for extracted corpora, local mirrors, tool payloads, or
non-provenance copies.

Do not add build products, virtualenvs, package caches, `.lake` build outputs,
or generated datasets unless a separate repo policy explicitly requires them.

When importing from an archive, preserve one of:

1. upstream git metadata and HEAD;
2. a manifest recording archive path, origin, HEAD, and tracked-file count;
3. a clear note that the directory is source-only and not a full checkout.

## Cloned From The 2026-06-06 Archive Audit

The following archive repos were not present under `external_refs/` at audit
time and were then cloned locally from `/media/goutev/SP DS72/auto/external`:

```text
atlas-embeddings
VirasoroProject
QuAIRKit
PauLie
affine-charform
RIA_EISA
```

They are nested git checkouts with upstream `origin` remotes and local `archive`
remotes. They are not yet staged as top-level submodules/gitlinks.

`pyw` is present as source but still lacks `.git` metadata.
