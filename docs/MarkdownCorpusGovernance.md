# Markdown Corpus Governance

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Last updated: 2026-05-02 (Europe/Sofia)

This document defines how Markdown is kept honest without rewriting the Black
Book chapters.

## Protected Exclusions

The cleanup lane does not rewrite:

- `docs/black_books/`
- `docs/black_books_refactor/`
- vendored dependency trees such as `.lake/`

## Canonical Rule

The Markdown corpus is not flat. A file being tracked does not make it current.

Current authority is limited to the maintained entry docs listed in:

- [README.md](README.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [../README.md](../README.md)

## Status Labeling

Repo-owned Markdown outside the protected exclusions is labeled into one of:

- `current authority`
- `maintained local guide`
- `reference memory`
- `generated/historical report`
- `archival reference`
- `historical handover`
- `workflow-local reference`

## Refresh Tool

Status blocks are maintained by:

- `python3 tools/docs/refresh_markdown_status.py`

That tool:

- skips protected Black Book paths
- skips vendored dependency trees
- preserves titles/content
- updates or inserts a short status block near the top of each file

## Practical Rules

1. Rewrite the small authority surface by hand when the codebase changes.
2. Use the status refresh tool to relabel the broader Markdown corpus.
3. Treat `reports/` as snapshots unless regenerated.
4. Treat `archive/` and `handover/` as provenance, not current policy.
5. If a document is not linked from the maintained entry surface, assume it is
   not current authority.
