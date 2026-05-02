# Docs Tools

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

This directory contains maintained documentation refresh helpers.

## Current Entrypoints

- `generate_auto_docs.py`
- `update_repo_docs.py`
- `refresh_markdown_status.py`

## Role Split

- `generate_auto_docs.py`
  owns generated doc surfaces under `docs/auto/`
- `update_repo_docs.py`
  refreshes selected derived documentation artifacts
- `refresh_markdown_status.py`
  relabels the wider Markdown corpus so stale files stop reading like current
  repository authority

## Rule

Use generators for generated docs and hand edits for the small maintained
authority surface.
