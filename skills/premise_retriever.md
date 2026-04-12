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
