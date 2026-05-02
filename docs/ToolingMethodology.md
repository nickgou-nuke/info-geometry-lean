# Tooling Methodology

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for tooling operations, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This is the practical operator runbook for the current toolchain.

## Default Rule

Use the smallest maintained command that answers the question.

## Normal Commands

Changed Lean work:

```bash
lake script run changedVerify
```

Current DAG health:

```bash
lake script run dagStatus
lake script run dagDoctor
```

Full refresh:

```bash
lake script run dagAll
```

Frontier/proof-state work:

```bash
lake script run proofSession
lake script run proofPrint -- <Decl.Name>
lake script run semanticSnapshot
```

LeanTrail carrier work:

```bash
lake script run leantrailConformance
lake script run leantrailExport
lake script run leantrailArangoIngest
lake script run leantrailArangoPhysicsEval
```

## Method Selection

Use `changedVerify` when:

- you edited Lean files
- you want the fastest trustworthy verification lane

Use `dagDoctor` when:

- reports look stale
- a graph surface seems inconsistent
- you want diagnosis before repair

Use `dagAll` when:

- you need fresh artifact and report surfaces for the repository as a whole

Use raw Python entrypoints only when:

- a Lake wrapper is failing
- you need narrower control for repair or debugging

## Artifact Rule

Do not treat `reports/` or `artifacts/` as current truth unless they were
regenerated for the question at hand.
