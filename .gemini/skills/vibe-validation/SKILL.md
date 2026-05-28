---
name: vibe-validation
description: Iterative AI-driven formalization for Lean 4. Use when porting algorithms (Rust/Python) to Lean, filling proof skeletons, or performing a clinical audit of AI-generated proofs to eliminate 'sorry' while maintaining symbolic rigor.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. **Zero Tolerance for Vacuous Scaffolding.** Never promote a vibe, physics analogy, semantic embedding, graph edge, or AI-generated proof sketch as a completed proof. Every promoted proposition must be discharged by a native Lean derivation chain rooted in Mathlib or current owner modules. Do not use opaque `Prop` fields, certificates, witnesses, or projection-only wrappers to resolve debt; real progress must be structural and verified by the kernel.

# vibe-validation

## Procedural Workflow for AI-Driven Formalization in Lean 4

This skill implements the **"Vibe Validation"** protocol for bridging informal software/physics logic to formal Lean 4 proofs. It is designed for use in the **Info-Geometry Spire** to eliminate `sorry` markers and vacuous placeholders while maintaining symbolic rigor.

### Core Workflow: The Clinical Refinement Loop

1.  **Plan**: Define the toy algorithm, base invariant, and exact Lean owner
    proposition before writing automation prompts.
2.  **Classify**: Mark each target as `proved math`, `open debt`,
    `false/wrong-target`, or `wrapper/vacuous`. Stop on false targets instead
    of weakening the theorem until it compiles.
3.  **Formalize**: Convert the informal claim or external code (Rust/Python) to
    Lean 4 declarations. **Use concrete identities, not vacuous laws.**
4.  **Checkpoint**: Use AI to suggest proof steps only after the proposition is
    meaningful. Accept `sorry` only as a temporary architectural placeholder,
    never as a permanent certificate.
5.  **Audit (The Pauli Mandate)**:
    - **Distrustful Audit**: Manually inspect AI-generated proofs for semantic
      drift, projection-only closure, trivialized premises, or simplification
      hacks. Ensure laws are not made trivial just to pass the checker.
    - **Visual Audit**: Use **Paperproof** to visualize the tactic tree and
      verify goal splitting; Paperproof is evidence for inspection, not proof
      authority by itself.
6.  **Replan/Golf**: Refine the proof to align with Mathlib idioms. Eliminate
    all `sorry` markers and redundant scaffolding in the agreed scope.

### Rules of Engagement (The Kadie Standards)

- **Rule 1: Invariants First**: Never change code representation without updating formal invariants.
- **Rule 2: Toy Baseline**: Prove a slow, obviously correct "toy" version before tackling optimized production logic.
- **Rule 3: Edge Case Pre-emption**: Address null/boundary cases early to simplify the inductive step.
- **Rule 4: Foundation Lifting**: Define basic sets/ranges in Lean before the core algorithm.
- **Rule 5: The Axiom-Surface Seal**: Audit the final result with `#print axioms` to ensure no axiomatic leakage or "fake" proof authority.

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
