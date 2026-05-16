---
name: paperproof-validator
description: Visual auditing and goal state inspection for Lean 4. Use when debugging complex tactic blocks, inspecting goal splitting behavior, or performing a visual 'Distrustful Audit' of AI-generated proofs to ensure nomological closure.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# paperproof-validator

## Visual Auditing and Tactic State Inspection for Lean 4

This skill enables the **Paperproof Validator** workflow within the **Info-Geometry Spire**. It transforms opaque tactic blocks into interactive proof trees to ensure nomological closure and eliminate "vibe-based" logical gaps.

### When to Use
- Auditing complex inductive proofs or deep tactic chains.
- Inspecting goal splitting behavior (e.g., `cases`, `induction`, `apply`).
- Verifying that all hypotheses are correctly utilized and no goals remain unproven.
- Performing a "Distrustful Audit" of AI-generated proof skeletons.

### Core Workflow: The Visual Audit
1.  **Instrument**: Add `import Paperproof` to the top of the target Lean module.
2.  **Activate**: Click the **Paperproof icon** in the VS Code editor title bar while inside a `by` block.
3.  **Inspect**:
    - **Green Nodes**: Hypotheses/Assumptions. Verify these match the intended physical invariants.
    - **Red Nodes**: Active Goals. These must be systematically eliminated.
    - **Dashed Nodes**: Tactics. Audit the effect of each tactic on the hypothesis state.
4.  **Verify Closure**: A proof is valid only when the Paperproof tree shows no remaining Red nodes and every branch terminates at an axiom or proven lemma.

### Clinical Standards (Pauli Integration)
- **Zero-Sorry Mandate**: Paperproof must be used to find the exact location of any `sorry` within a complex proof tree.
- **Tactic Parsimony**: If Paperproof reveals excessive goal splitting or redundant tactics, use the `/lean4 golf` command to simplify the proof.
- **Semantic Fidelity**: Cross-reference the visual tree with the original math/physics definitions to ensure the "Multilingual Bridge" is intact.

### Tool Configuration
- **Lean Version**: Pins to `v4.28.0`.
- **VS Code Extension**: Requires version `v2.7.0` (matching our toolchain).
- **Lake Integration**: Added via `require paperproof` in `lakefile.lean`.

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
