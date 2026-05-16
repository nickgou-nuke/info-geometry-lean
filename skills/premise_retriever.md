# Skill: Premise Retriever

> **"Reason from facts, not from memory fragments."**

## Objective
Retrieve at least three relevant premises (lemmas, definitions, or constants) before generating any tactic or proof-step.

## Guidelines
1.  **Search First**: Never guess the name of a Mathlib lemma. Use the `trace_and_retrieve.py` tool to search for keywords.
2.  **Context Loading**: When a goal is presented, use the `retrieve` tool on the goal's types (e.g., `Module.End K V`, `Spectrum`) to find local Spire bedrock.
3.  **Premise Budgeting**: Keep the retrieved premise packet small and relevant. Prioritize **Bedrock** (L1-L3) over generic Mathlib.
4.  **Verification**: If a retrieved premise seems incorrect, re-query with more specific binders.

## Tools
- `tools/infra/trace_and_retrieve.py`: The primary engine for finding constants and proof-states.
- `grep`: Use for local repository keyword searching.

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
