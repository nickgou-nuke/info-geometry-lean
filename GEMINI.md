# Gemini Use Policy

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for optional ideation workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This file describes how Gemini-style ideation fits into the current repository
workflow.

## Current Role

Gemini-like exploration is optional and proposal-only.

It may help with:

- brainstorming candidate bridges
- external literature distillation
- packet enrichment before formal implementation

It does not decide theorem truth, module ownership, or closure status.

## Boundary

If a Gemini-generated idea matters, it must be translated into:

- a current owner file
- a concrete Lean or tooling change
- a current verification step

Without that translation, it stays exploratory.

## Authority Order

1. current code in `lean/`, `src/igf/`, and maintained `tools/`
2. current repo-level docs
3. optional ideation sidecars such as Gemini workflows
