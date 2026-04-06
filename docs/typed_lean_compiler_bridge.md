# Typed Lean Compiler Bridge Contract

This document records a proposed typed RPC contract for proof-state interaction
with Lean.

It is a design note, not an implemented current interface.

## Current substrate

The repository already has working server/export patterns that any future proof
bridge should reuse:

- `lean/DAG/SemanticServerRpc.lean`
- `lean/DAG/ServerExport.lean`
- `lean/DAG/BlockExport.lean`

These are the right precedents for transport and typed payloads. What they do
not yet provide is a proof-state contract for autonomous theorem generation.

## Problem statement

Current automation in the repo is strong on:

- semantic block export
- DAG and architecture reports
- file and declaration audits

It is weak on proof-state interaction. There is no maintained typed bridge for:

- opening a theorem session;
- reading structured goals and local hypotheses;
- applying proof steps with structured diffs; or
- classifying elaboration errors in machine-readable form.

## Minimal useful contract

If this bridge is built, the minimal shipping surface should be:

1. `openSession`
2. `checkSnippet`
3. `getGoals`
4. `runTactic`
5. `validateDecl`
6. `closeSession`

All payloads should be typed, versioned, and deterministic with respect to the
current environment fingerprint.

## Design constraints

- Reuse Lean server RPC, do not invent a second process model.
- Keep the kernel as source of truth.
- Return structured errors, not raw strings only.
- Return semantic diffs after proof actions where possible.
- Keep this bridge separate from the repository’s DAG/report pipeline.

## Suggested payload direction

The important requirement is not the exact schema below, but the semantic shape:

- session identity
- environment fingerprint
- typed goal views
- typed local declaration views
- classified compiler errors
- validation result without `sorry`

Any future implementation should preserve those invariants.

## Current repository priority

This bridge is still future infrastructure.

It should not outrank the current mathematical closure work on:

- realized generalized-metric projectors;
- polarized and recomposition junction closure;
- operator-level anomaly/Weyl welding; and
- count/projective attachment at the polarized carrier.

If work starts here later, it should reuse the current DAG/server substrate and
be introduced in a narrow first phase rather than as a large umbrella service.
