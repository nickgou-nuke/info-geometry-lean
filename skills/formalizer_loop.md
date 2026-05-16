# Skill: Formalizer Loop

> **"Iterate until closure. Search until proof."**

## Objective
Implement an iterative proof-generation and repair loop using **LeanCopilot** and **LeanDojo-v2** interaction methodologies.

## Guidelines
1.  **LeanDojo-v2 Goal Retrieval**: Use the programmatic bridge to extract the current Lean goal state (Goal Conditioned Reasoning). 
2.  **LeanCopilot Tactic Suggestion**: Use `search_proof` or `select_premises` logic to propose tactics based on the current goal and the **Premise Packet**.
3.  **REPL Feedback**: Execute tactics via the REPL. 
    - If successful, move to the next state in the **Chain of States**.
    - If failure, analyze the error (e.g., "unknown identifier") and re-query the `PremisePacket` via `select_premises`.
4.  **Audit Awareness**: No step is final until the goal state is `No goals`. No `sorry` is permitted in the final trace.
5.  **Refactoring**: Once the goal is closed, distill the result into a dense proof term as defined by the Constitution.

## Tools
- `tools/infra/lean_interact_wrapper.py`: The REPL bridge (LeanDojo-v2 compatible).
- `skills/premise_retriever`: To fetch new facts for repair.

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
