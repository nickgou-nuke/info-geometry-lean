# Skill: Statement Compiler

> **"A compiling signature is the first Victory of Unity."**

## Objective
Generate and repair Lean 4 declaration signatures (headers) based on a **Theorem Packet**.

## Guidelines
1.  **Drafting**: Convert the `informalGoal` from the Source Packet into a formal Lean 4 `theorem` or `def` header.
2.  **Signature Repair**: Run `lake build` or use the `LeanInteract` REPL to verify the signature. 
    - Fix universe parameters, binders, and missing imports.
    - DO NOT write the proof-body yet; use `sorry` or `constant` for the body during this stage.
3.  **Namespace Alignment**: Ensure the declaration is placed within the correctly qualified Spire namespace (e.g., `InfoGeometry.Canonical.Drazin`).
4.  **Audit Lock**: Once the signature compiles, freeze it. No further changes to the header are allowed during the formalization loop.

## Tools
- `LeanInteract`: To verify signature compilation.
- `lake`: For full-project build verification.

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
