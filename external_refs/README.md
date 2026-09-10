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
Canonical
CanonicalLean
NavierStokesAndEuler
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

`external_refs/Canonical` is a full-history nested checkout at `dbd175b` from
`https://github.com/chasenorman/Canonical.git`. The root is a Rust workspace
for exhaustive term search in dependent type theory, with `canonical-core`,
`canonical-compat`, and `canonical_lean` Lean FFI bindings. Its Lean test
project lives under `lean/`, pins `leanprover/lean4:v4.30.0`, and depends on
`CanonicalLean` and mathlib at `v4.30.0`.

`external_refs/CanonicalLean` is a full-history nested checkout at `65510e4`
from `https://github.com/chasenorman/CanonicalLean.git`. It is the Lean package
named `Canonical`, provides the `canonical` tactic, pins
`leanprover/lean4:v4.30.0`, and defines a release-fetched `canonical_lean`
dynlib target in `lakefile.lean`. The related project homepage is
`https://chasenorman.com/`.

`external_refs/NavierStokesAndEuler` is a full-history nested checkout at
`8937a8f4` from `https://github.com/openai/NavierStokesAndEuler.git`. It contains
the complete formalization of finite-time blowup for the 3D incompressible
Euler and Navier-Stokes equations (2,486 Lean 4 files, 72,536 lines), verified
with Mario Carneiro's Nanoda and DeepMind's Comparator (0 sorry, 0 custom
axioms). Its toolchain pins `leanprover/lean4:v4.34.0-rc2`. The native bridge
connecting its wave-packet Reynolds stress, Admissible Stress Cone, and
hyperbolic torus automorphism to our split-octonionic Zorn matrix algebra and
Madelung quantum fluid is formalized in
`InfoGeometry/Canonical/ZornNavierStokesHydrodynamicBridge.lean`.

As of the 2026-09-10 follow-up audit, all nested git checkouts under
`external_refs/` and `external/` are full-history checkouts:

```text
total_git_repos = 97
shallow_count = 0
```

`pyw` is present as source but still lacks `.git` metadata.
