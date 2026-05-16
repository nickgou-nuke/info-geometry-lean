# Heartbeat Policy Contract

Effective date: **2026-04-12**

Heartbeat is allowed for proof orchestration, not for autonomous public action.

## Allowed Planes

- Heartbeat may run only in `prove` or `orchestrate` planes.
- Heartbeat is forbidden in `publish` plane.

## Required Behavior

- On policy rejection, heartbeat cycles must emit a typed blocker and stop escalation.
- All outbound writes require publish gate approval.

## Blocker Types

- `policy_rejection`
- `proof_failure`
- `permission_denied`

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
