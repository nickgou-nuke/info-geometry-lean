# The Spire's Proof-Orchestration Constitution

> **"The kernel is the judge; the manifest is the law; the agent is the hand."**

This document defines the clinical standards for automated theorem formalization within the Info-Geometry Spire. It is meant to be mounted read-only into any agentic execution environment (Hermes Agent).

## I. The Absolute Lock (Non-Mutation Policy)
1.  **Identity Preservation**: An agent may never mutate the **Name**, **Universe Parameters**, or **Type Signature** of a theorem specified in a locked `task.json` manifest.
2.  **Failure over Drift**: If an agent cannot discharge a proof under the locked signature, it must report a **Blocking Debt** rather than adapting the statement to fit the proof.

## II. The Sieve of Pauli (Constructivity & Vacuity)
1.  **Zero-Sorry Rule**: No patch is accepted if it introduces a `sorry` or an `axiom`.
2.  **No Lyrical Inflation**: The use of "Surrogate Proofs" (rfl-tautologies that mask missing logic) is a violation of the constitution. Every bridge must be a functorial necessity.
3.  **Witness-Elimination**: Agents are mandated to use **Certified Global Constructors** (e.g., `drazinInverse`) rather than local existential witnesses wherever the bedrock exists.

## III. The Redlines (Environmental Limits)
1.  **Import Entropy**: An agent may not add new `import` statements to a file unless they are explicitly permitted in the `task_manifest.json` budget.
2.  **Dependency Hygiene**: Accidental use of `Classical.choice` or extensionality lemmas on types where constructive alternatives exist is forbidden.
3.  **Namespace Qualification**: All constants must be fully qualified (e.g., `InfoGeometry.Canonical.Drazin.IsDrazinInverse`) to prevent resolution drift.

## IV. The Promotion Protocol
1.  **Quarantine**: Successful builds are initially stored in `quarantine/winning_traces.jsonl`.
2.  **Auto-Promotion**: A trace is promoted to `validated_patterns.jsonl` only after passing the **Triple Gate**:
    - **Gate 1**: Clean Build (`lake build`).
    - **Gate 2**: Semantic Audit (`semantic_audit.py` showing zero signature drift).
    - **Gate 3**: Replay Success (Verified patch application in a fresh checkout).

## V. Asymmetric Role Separation
1.  **The Proposer**: Responsible for high-level strategy, naming, and dependency selection. It must prioritize conceptual integrity over compiler closure.
2.  **The Formalizer**: Responsible for the low-level tactic flow and goal-closing. It must prioritize kernel-compliance and proof-term density.
3.  **Role Isolation**: No single agent may claim both roles for a given proof-task to prevent self-confirmation drift.

---

**"Durch den Logos zur Wahrheit; durch das Gesetz zur Form."**
*(Through the Logos to Truth; through the Law to Form.)*
