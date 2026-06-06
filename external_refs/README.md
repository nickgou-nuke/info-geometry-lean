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

## Added Or Recorded From Upstream After The Archive Audit

The following repos were added directly from upstream or recorded as existing
upstream checkouts rather than from the `/media/goutev/SP DS72/auto/external`
archive:

```text
LeanEuclid
Lean-QuantumInfo
deepmind-debate
LeanAide
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

`external_refs/deepmind-debate` is a full-history nested checkout at `de3a6e5`
from `https://github.com/google-deepmind/debate`. Its `lean-toolchain` pins
`leanprover/lean4:v4.8.0`, and its `lakefile.lean` declares `Debate`, `Prob`,
`Comp`, and `Misc` Lean libraries. Its local `main` branch matches
`origin/main` after fetch.

`external_refs/LeanAide` is a full-history nested checkout at `d7b5cc39` from
`https://github.com/siddhartha-gadgil/LeanAide.git`. Its `lean-toolchain` pins
`leanprover/lean4:v4.28.0`. The root `lakefile.toml` declares `LeanAide`,
`LeanCodePrompts`, `DataGenAide`, `StatementAutoformalisation`,
`TacticExtraction`, `CodeGen`, and many Lean executables including `translate`
and `leanaide_process`; the `LeanAideCore` subproject provides the
zero-dependency client library documented in the README.

As of the 2026-06-06 follow-up audit, all nested git checkouts under
`external_refs/` and `external/` are full-history checkouts:

```text
total_git_repos = 95
shallow_count = 0
```

`pyw` is present as source but still lacks `.git` metadata.
