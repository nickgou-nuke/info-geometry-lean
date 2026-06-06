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
remotes. They were unshallowed after cloning. They are not yet staged as
top-level submodules/gitlinks.

## Added Directly From Upstream After The Archive Audit

The following repo was added directly from upstream rather than from the
`/media/goutev/SP DS72/auto/external` archive:

```text
LeanEuclid
Lean-QuantumInfo
```

`external_refs/LeanEuclid` is a full-history nested checkout at `7c8f38b` from
`https://github.com/loganrjmurphy/LeanEuclid.git`. Its `lean-toolchain` pins
`leanprover/lean4:v4.19.0`, and its `lakefile.lean` declares `SystemE`, `Book`,
`UniGeo`, and `E3` Lean libraries.

`external_refs/Lean-QuantumInfo` is a full-history nested checkout at
`56e83a9` from `https://github.com/Timeroot/Lean-QuantumInfo.git`. Its
`lean-toolchain` pins `leanprover/lean4:v4.28.0`, and its `lakefile.lean`
declares `QuantumInfo`, `ClassicalInfo`, and `StatMech` Lean libraries. Its
README says this work merged into Physlib after March 2026, so treat this as a
reference snapshot unless we deliberately port selected theorem material.

As of the 2026-06-06 follow-up audit, all nested git checkouts under
`external_refs/` and `external/` are full-history checkouts:

```text
total_git_repos = 93
shallow_count = 0
```

`pyw` is present as source but still lacks `.git` metadata.
