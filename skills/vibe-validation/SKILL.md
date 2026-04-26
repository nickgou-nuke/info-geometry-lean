---
name: vibe-validation
description: Iterative AI-driven formalization for Lean 4. Use when porting algorithms (Rust/Python) to Lean, filling proof skeletons, or performing a clinical audit of AI-generated proofs to eliminate 'sorry' while maintaining symbolic rigor.
---

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
