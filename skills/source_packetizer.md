# Skill: Source Packetizer (The Distiller)

> **"Structure serving Discovery. The Distiller converts Ore to Manifest."**

## Objective
Act as the primary interface between the Generative Forge and the Constitutional Sieve. Distill refined theorem candidates into the strict **JSON Manifest** required for Stage-2 Certification.

## Guidelines
1.  **Distillation**: Take the output of the `Adversarial Compressor` and map it into the strict `docs/policy/packet_schemas.md` format.
2.  **Signature Hardening**: Ensure the `expectedType` is consistent with the Spire's global namespace and current commit-indexed trace.
3.  **Hygienic Preparation**: Identify the minimum `budget.imports` and `budget.witnesses` required to discharge the proof in Regime B.
4.  **Provenance Lock**: Record the discovery provenance (e.g., "Origin: Regime A, Forge Session <ID>").

## Handshake
Produce a **Locked Task Manifest** (`.tasks/*.json`) and a **Chain of States**.

## Tools
- `tools/infra/trace_and_retrieve.py`: Use to generate the **Premise Packet** for the distiller.
- `ls`: Use to verify target file placement.

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
