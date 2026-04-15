# Copyright Surface Inventory (Tracked Repo)

Generated from an exhaustive tracked-file regex scan:

```bash
git ls-files -z | xargs -0 rg -nIH -m 1 -i \
  "copyright|all rights reserved|licensed under|spdx-license-identifier|community license|gnu lesser general public license|proprietary"
```

Snapshot date (UTC): 2026-04-15

## Summary

- Total hits: 44
- Top-level distribution:
  - `external_refs/`: 9 hits (primary third-party code zone)
  - `docs/`: 3 hits (policy/content text, not necessarily code imports)
  - `.agents/`: 2 hits (workflow documentation text)
  - repo legal files: `LICENSE`, `NOTICE`
- Additional project-owned headers in `lean/**` and `skills/**`.

## High-confidence third-party zones

### 1) `external_refs/llama4/**`

Observed direct vendor headers such as:

- `Copyright (c) Meta Platforms, Inc. and affiliates.`
- `All rights reserved.`
- references to Llama community license terms

Action:

- Keep out of public-source release bundles unless legal review approves.
- Already excluded from archive bundles via `tools/infra/archive_excludes.txt`.

### 2) `interspec_src/**` (external payload)

Observed LGPL/copyright notices from external owners.
This directory was moved out of the repository working tree.

## Project-owned legal surface

- `LICENSE`: Apache-2.0 license text.
- `NOTICE`: project copyright:
  - Nikolay Goutev
  - Dimitar Tonev
- `CITATION.cff`: citation and repository metadata.
- `lean/**` headers with project copyright.

## Recommended lane split

1. **Evidence lane (internal):**
   - use `tools/infra/create_evidence_bundle.sh --full-state`
   - optionally keep build artifacts and compiled state.

2. **Public release lane (source-first):**
   - use `tools/infra/create_evidence_bundle.sh --source-only`
   - keep `tools/infra/archive_excludes.txt` active.
   - include stubs/README notes for excluded external zones when publishing.

## Current exclusion policy file

`tools/infra/archive_excludes.txt`

- `external_refs/`
- `interspec_src/`

