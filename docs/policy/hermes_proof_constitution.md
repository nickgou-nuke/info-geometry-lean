# The Spire's Proof-Orchestration Constitution

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../../README.md), [docs/README.md](../README.md), [docs/CODEBASE_STATUS.md](../CODEBASE_STATUS.md)

> **"The kernel judges, the manifest legislates, the agent executes."**

This document defines the clinical standards for automated theorem formalization within the Info-Geometry Spire. It is the authoritative law for the proof-orchestration loop.

## I. The Absolute Lock (Audit Rule 1)
1.  **Identity Preservation**: The agent must preserve the **Name**, **Universe Parameters**, and **Type Signature** specified in the locked manifest.
2.  **Debt Policy**: Failure to prove the locked statement constitutes **blocking debt**, not license to redesign. 

## II. The Sieve of Pauli (Audit Rule 2)
1.  **Zero-Sorry**: No patch is accepted that introduces `sorry` or `axiom`.
2.  **Constructive Bedrock**: Use of `Classical.choice`, `by_contra`, or nonconstructive extensionality lemmas is forbidden unless explicitly permitted by the task manifest.
3.  **Canonical Weight**: Agents must prefer repository-certified global constructors and canonical existence bridges over ad hoc local existential witnesses whenever such bedrock already exists.

## III. Environmental Hygiene (Audit Rule 3)
1.  **Import Lockdown**: A patch may not alter the import budget of a file unless authorized by the manifest.
2.  **Qualified Names**: Locked theorem targets, exported declarations, and audit-relevant constants must be fully qualified where ambiguity is possible.
3.  **Surface Stability**: The agent may not alter namespace boundaries or surrounding declaration surfaces unless explicitly authorized.

## IV. The Promotion Protocol (Audit Rule 4)
Promotion to `validated_patterns.jsonl` is authorized only for traces that satisfy the **Triple Gate**:
1.  **Kernel Verity**: Successful build on a clean environment.
2.  **Semantic Stability**: Zero drift in theorem identity, declaration surface, and import budget.
3.  **Replay Success**: Successful patch application and re-build on a fresh checkout.

## V. Asymmetric Role Separation (Audit Rule 5)
1.  **The Proposer**: Responsible for proof decomposition, helper naming, and dependency proposal.
2.  **The Formalizer**: Responsible for low-level tactic flow and goal-closing.
3.  **Execution Isolation**: No single execution context may claim both roles for the same locked proof task.

---

**"Durch den Logos zur Wahrheit; durch das Gesetz zur Form."**
