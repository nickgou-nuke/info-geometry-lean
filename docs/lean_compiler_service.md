# Typed Lean Compiler Service

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This note is a future infrastructure design document.

It does not describe a fully implemented current service. It records what the
repo already has, what is still missing, and what a typed compiler-facing
service would need if autonomous theorem synthesis becomes a first-class
workflow.

## Current state

The repository already has strong semantic export infrastructure for declarations
and dependency structure:

- `lean/DAG/SemanticServerRpc.lean`
- `lean/DAG/ServerExport.lean`
- `lean/DAG/BlockExport.lean`
- `lean/DAG/Indexer.lean`
- `lean/DAG/ProcessFlowExport.lean`
- `lean/DAG/RepresentationDepthExport.lean`
- `lean/InfoGeometry/Meta/Architecture.lean`
- `lean/InfoGeometry/Meta/Vacuity.lean`

These surfaces are real and useful, but they are declaration-graph and
block-export oriented. They are not yet a typed proof-state service for local
interactive theorem synthesis.

## What is missing

The missing layer is a proof-oriented semantic API that can expose:

- current goals with stable identity
- local context in structured form
- metavariable state
- elaboration failures with stable error kinds
- incremental semantic diffs after candidate proof steps
- deterministic replay within a Lean session

Without this layer, autonomous proving still falls back to text scraping and
stringly prompts at the proof-state boundary.

## Why this matters here

This repository already uses semantic export and architecture diagnostics as
normal infrastructure. A typed compiler service would be the proof-state
analogue of that existing DAG stack.

The actual need is practical:

- preserving semantic identity across refactors;
- classifying failures by type, not by regex on error strings;
- making theorem-search loops consume stable machine-readable proof state.

## Proposed service shape

If built, the service should sit on top of the existing Lean server and RPC
patterns rather than creating a second process model.

Suggested module family:

- `InfoGeometry.Agent.Protocol` (proposed)
- `InfoGeometry.Agent.ExprCodec` (proposed)
- `InfoGeometry.Agent.ProofStateExport` (proposed)
- `InfoGeometry.Agent.ElabTraceExport` (proposed)
- `InfoGeometry.Agent.ProofServerRpc` (proposed)

These are target module names, not current files in the repository tree.

Minimal capability set:

1. open theorem/session
2. get typed proof state
3. apply candidate term or tactic
4. classify the resulting error or state change
5. validate the final declaration

## Repository-grounded constraint

This service should be additive to the current repo workflow, not a replacement
for it.

It must fit around:

- `lake build`
- strict checks
- vacuity and architecture audits
- DAG export and report generation

The compiler service would be the local interactive layer. The current DAG and
policy stack would remain the outer validation layer.

## Current priority

This is not the immediate closure task for the repository.

Current mathematical closure work is still ahead of this service work:

1. internalize realized-projector to tomita-projector identification;
2. derive projector obstruction from trunk-compatible operator data;
3. finish the Weyl operator weld; and
4. attach the count/projective trunk at polarization.

So this note should be read as future infra planning, not as an active
implementation commitment.

## Related blueprint

For the reviewer-facing control plane and private Socratic interrogation surface
that can sit above this proof infrastructure, see:

- [private_reviewer_chat_blueprint.md](private_reviewer_chat_blueprint.md)

That blueprint covers identity, room policy, gateway/tool governance, audit
trails, and phased rollout. This file remains focused on typed proof-state RPC.
