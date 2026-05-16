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

## UTMOST MANDATE: Native Lean proof closure over witness/certificate temporary scaffolding (Native Closure Mandated: Closure Debt)

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate field (Native Closure Mandated: Closure Debt)s, external certificates, and assumption interfaces are temporary temporary scaffolding (Native Closure Mandated: Closure Debt) only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
