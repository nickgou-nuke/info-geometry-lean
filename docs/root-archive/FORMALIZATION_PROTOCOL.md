# Lean Formalization Protocol

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This is the current practical protocol for turning an idea into checked Lean in
this repository.

## Core Rule

Never formalize directly from visionary prose, old reports, or graph proximity.
Formalize from:

- current Lean owner files
- explicit hypotheses you can state in Lean
- direct local build feedback

## Workflow

1. Find the current owner surface in `lean/`.
2. Read direct consumers before inventing new abstractions.
3. State the smallest theorem or definition that matches the existing owner
   structure.
4. Build the changed file first with `lake env lean`.
5. Build the owner module or use `lake script run changedVerify`.
6. Only after the code is coherent, refresh broader graph/report surfaces.

## Current Verification Commands

Fast local loop:

```bash
lake env lean <changed-file>.lean
lake build <Owner.Module>
```

Repo-managed verification:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

## Translation Discipline

If the input is conceptual prose, external math language, or old repo doctrine,
first convert it into:

- owned definitions already present in `lean/`
- explicit assumptions
- a target file and target declaration shape
- open debt that remains non-formalized

If you cannot name the owner file, you are not ready to formalize.

## What Not To Do

- do not let a capstone file invent lower mathematics
- do not use generated reports as proof authority
- do not preserve a wrapper just because it sounds important
- do not treat stale docs as a specification when the code says otherwise
