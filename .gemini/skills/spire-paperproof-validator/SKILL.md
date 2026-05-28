---
name: spire-paperproof-validator
description: Visual auditing and goal state inspection for Lean 4. Use when debugging complex tactic blocks, inspecting goal splitting behavior, or performing a visual 'Distrustful Audit' of AI-generated proofs to ensure nomological closure.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. **Kernel-Checked Evidence Only.** Paperproof is an inspection aid for checking that proof branches terminate in genuine Lean evidence, not vacuous placeholders. Never use visual clarity to obscure a lack of symbolic rigor. Every node in the tree must represent a valid step toward kernel-checked closure, and final authority remains the Lean kernel plus explicit axiom-surface audit.

# paperproof-validator

## Visual Auditing and Tactic State Inspection for Lean 4

This skill enables the **Paperproof Validator** workflow within the **Info-Geometry Spire**. It transforms opaque tactic blocks into interactive proof trees to ensure nomological closure and eliminate "vibe-based" or vacuous logical gaps.

### When to Use
- Auditing complex inductive proofs or deep tactic chains (e.g., $N=2$ supercharge transport).
- Inspecting goal splitting behavior to ensure no sub-goals are bypassed by "semantic cheating".
- Verifying that all hypotheses are correctly utilized to derive concrete mathematical identities.
- Performing a "Distrustful Audit" of AI-generated proof skeletons to detect "empty" proof paths.

### Core Workflow: The Visual Audit
1.  **Instrument**: Add `import Paperproof` to the top of the target Lean module.
2.  **Activate**: Click the **Paperproof icon** in the VS Code editor title bar while inside a `by` block.
3.  **Inspect**:
    - **Green Nodes**: Hypotheses/Assumptions. Verify these are mathematically robust and not just vacuous `Prop` fields.
    - **Red Nodes**: Active Goals. These must be systematically eliminated via native Lean tactics.
    - **Dashed Nodes**: Tactics. Audit the effect of each tactic on the hypothesis state.
4.  **Verify Closure**: A proof is valid only when the Paperproof tree shows no remaining Red nodes and every branch terminates at a proven lemma, definitional equality, or allowed Mathlib/root theorem. Do not accept custom axioms, arbitrary field projections, or `True`/`trivial` endpoints as closure.

### Clinical Standards (Pauli Integration)
- **Zero-Sorry Mandate**: Paperproof must be used to find and eliminate the exact location of any `sorry` or "fake" root.
- **Structural Integrity**: Cross-reference the visual tree with the non-vacuous definitions in files like `UnnormalizedRelativeEntropy.lean` to ensure the derivation is sound.
- **Axiom-Surface Seal**: Ensure the proof tree does not leak into custom axioms; it must be rooted in Mathlib or project-local proven lemmas.
