# Copyright / Third-Party Exclusion Audit

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Date (UTC): 2026-04-15

## Objective

Identify non-project code that should be excluded from legal evidence source archives.

## Findings

### 1) `interspec_src/` (moved out of repo)

- Size observed before move: ~100 MB.
- Contains third-party InterSpec source files with external copyright/license headers.
- Action taken: directory moved outside the repository tree.
- Relocation path:

```text
/tmp/info-geometry-external-20260415T193443Z/interspec_src
```

### 2) `external_refs/` (retained as reference material, excluded from archive)

Detected third-party license/copyright markers, including:

- Meta/Llama license headers in `external_refs/llama4/**`
- Additional non-project reference content under `external_refs/**`

Action taken:

- Archive generation now excludes `external_refs/` via `tools/infra/archive_excludes.txt`.

## Archive exclusion policy

`tools/infra/archive_excludes.txt` currently contains:

- `external_refs/`
- `interspec_src/`

This list is consumed automatically by:

```text
tools/infra/create_evidence_bundle.sh
```

## Verification commands

```bash
tools/infra/create_evidence_bundle.sh --ref HEAD --out-dir /tmp/info-geometry-evidence-test
tools/infra/verify_evidence_bundle.sh /tmp/info-geometry-evidence-test
```
