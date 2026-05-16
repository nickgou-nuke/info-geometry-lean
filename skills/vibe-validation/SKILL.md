---
name: vibe-validation
description: Iterative AI-driven formalization for Lean 4. Use when porting algorithms (Rust/Python) to Lean, filling proof skeletons, or performing a clinical audit of AI-generated proofs to eliminate 'sorry' while maintaining symbolic rigor.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# vibe-validation

## Procedural Workflow for AI-Driven Formalization in Lean 4

This skill implements the **"Vibe Validation"** protocol for bridging informal software/physics logic to formal Lean 4 proofs. It is designed for use in the **Info-Geometry Spire** to eliminate `sorry` markers while maintaining symbolic rigor.

### Core Workflow: The Clinical Refinement Loop

1.  **Plan**: Define the "toy" algorithm or base invariant. Establish the semantic meaning before implementation.
2.  **Formalize**: Convert the informal claim or external code (Rust/Python) to Lean 4 declarations.
3.  **Checkpoint**: Use AI to fill the proof skeleton. Accept `sorry` only as a temporary architectural placeholder.
4.  **Audit (The Pauli Mandate)**:
    - **Distrustful Audit**: Manually inspect AI-generated proofs for "semantic drift" or simplification hacks.
    - **Visual Audit**: Use **Paperproof** to visualize the tactic tree and verify goal splitting.
5.  **Replan/Golf**: Refine the proof to align with Mathlib idioms. Eliminate all `sorry` markers.

### Rules of Engagement (The Kadie Standards)

- **Rule 1: Invariants First**: Never change code representation without updating formal invariants.
- **Rule 2: Toy Baseline**: Prove a slow, obviously correct "toy" version before tackling optimized production logic.
- **Rule 3: Edge Case Pre-emption**: Address null/boundary cases early to simplify the inductive step.
- **Rule 4: Foundation Lifting**: Define basic sets/ranges in Lean before the core algorithm.
- **Rule 5: The Axiom-Surface Seal**: Audit the final result with `#print axioms` to ensure no axiomatic leakage.

### Tool Integration: Paperproof

Paperproof visualizes Lean proofs as interactive trees. Use it to audit complex goal states.

- **Setup**: Ensure `import Paperproof` is in the module.
- **Visualization**: Click the Paperproof icon in the editor to inspect:
    - **Green**: Hypotheses.
    - **Red**: Current goals.
    - **Dashed**: Tactics applied.
- **Audit Criterion**: Every branch in the Paperproof tree must terminate in a closed proof (no `sorry`).

### Commands & Automation
Refer to the `lean4-skills` scripts for automated proof filling:
- `draft <informal_text>`: Generates Lean signature.
- `prove <decl_name>`: Initiates autonomous proof search via Mathlib.
- `golf <decl_name>`: Simplifies and audits tactic blocks.

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
