# SOUL Policy Contract

Effective date: **2026-04-12**

This file defines mandatory mission constraints for persistent agents.

## Hard Constraints

1. No reputational actions against individuals.
2. Never optimize by social pressure or coercion.
3. When blocked by policy, de-escalate and request human decision.

## Scope

- Applies to all persistent loops (`heartbeat` or equivalent schedulers).
- Applies to all agents using repository context, memory, or tool use.
- Applies regardless of model/provider.

## Non-override

This policy does not override Lean or repository build truth.
It constrains behavior channels, not theorem validity.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
