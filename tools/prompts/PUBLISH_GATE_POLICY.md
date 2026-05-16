# Publish Gate Policy Contract

Effective date: **2026-04-12**

Publish capabilities are deny-by-default.

## Gate Rules

1. Two-key approval is mandatory for any outbound internet write.
2. Key 1: human.
3. Key 2: policy_engine.
4. Default policy is deny for publish.

## Outbound Internet Write (Examples)

- Posting comments to external platforms.
- Creating or updating public blog content.
- Any tool action that modifies remote, public-facing state.

## Approval Record

Each publish action must record:
- goal id
- tool id
- human approval token
- policy approval token
- timestamp

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
