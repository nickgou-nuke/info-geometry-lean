# Operational Intent

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This repository is maintained as code first, prose second.

The purpose of the documentation layer is to help people recover the live code
surface quickly without mistaking old reports or conceptual notes for current
truth.

## Intent

The active repository has two jobs:

- formalize mathematics in Lean under `lean/`
- build reproducible artifact and audit tooling around that code under
  `src/igf/` and `tools/`

It has a third active layer as well:

- generate new theorem pressure through structured LLM dialogue, Socratic
  regeneration, and packetized ideation before formal closure

It has a fourth live discipline coupled to that layer:

- Pauli-style anti-inflation pressure that asks whether a candidate is even
  true before it is allowed to climb toward authority

The repo is not trying to make Markdown the final authority. The final
authority is the checked-in code and the verifiable outputs generated from it.

## Working Rules

- Lean source owns theorem claims
- Pauli differentiation blocks decorative or underived ascent before theorem claims
- Python and Lake scripts own reproducible artifact workflows
- generated reports are snapshots, not policy
- historical docs stay available, but labeled as such
- Black Book chapters remain protected exploration material

## Why The Markdown Cleanup Happened

The repository had accumulated a large amount of stale prose, generated reports,
and historical runbooks that still looked current. That created a false sense
of certainty.

The 2026-05-02 cleanup resets the contract:

- a small maintained core of docs describes the live codebase
- the rest of the corpus is explicitly marked as generated, historical, local,
  or reference memory

## Operational Reading Order

1. [../README.md](../README.md)
2. [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
3. [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
4. [ModuleMap.md](ModuleMap.md)
5. [GenerativeDiscoveryArchitecture.md](GenerativeDiscoveryArchitecture.md)
6. [../tools/README.md](../tools/README.md)
7. [../tools/infra/README.md](../tools/infra/README.md)

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
