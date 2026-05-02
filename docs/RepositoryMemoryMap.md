# Repository Memory Map

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This file tells you which repository surfaces are current, generated, or merely
kept as memory.

## Trust Order

When sources disagree, trust:

1. `lean/` and `lakefile.lean`
2. `src/igf/` and maintained scripts under `tools/`
3. [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
4. maintained entry docs
5. generated reports
6. historical notes, handover packets, and archives

## Current Authority

These are the maintained entry surfaces:

- [../README.md](../README.md)
- [README.md](README.md)
- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
- [ModuleMap.md](ModuleMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [GeneratedArtifactsPolicy.md](GeneratedArtifactsPolicy.md)
- [MarkdownCorpusGovernance.md](MarkdownCorpusGovernance.md)
- [OperatorQuickstart.md](OperatorQuickstart.md)
- [DAGTroubleshooting.md](DAGTroubleshooting.md)
- [LeanTrail.md](LeanTrail.md)
- [../Installation.md](../Installation.md)
- [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
- [../tools/README.md](../tools/README.md)
- [../tools/infra/README.md](../tools/infra/README.md)
- [../leantrail/README.md](../leantrail/README.md)

## Generated Surfaces

These are reproducible outputs, not hand-maintained truth:

- `docs/auto/`
- `reports/`
- `artifacts/`
- run-specific Markdown under generated output trees

Treat them as snapshots. Regenerate before relying on them.

## Historical And Reference Surfaces

These remain useful, but are not current authority:

- most non-entry docs under `docs/`
- `archive/`
- `handover/`
- top-level protocol and memo files
- local workflow docs under `.agents/workflows/`

Use them as context, not as policy.

## Protected Exploration Surface

The following subtree is intentionally protected from rewrite cleanup:

- `docs/black_books/`

It is part of the repository’s exploration layer, not the operational authority
layer.
