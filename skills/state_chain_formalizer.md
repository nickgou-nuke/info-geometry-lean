# Skill: State-Chain Formalizer

> **"Closure is a sequence of transformations, not a single leap."**

## Objective
Decompose complex formalization tasks into a **Chain of States** (intermediate lemmas or sub-goals) before generating final tactics.

## Guidelines
1.  **Skeleton First**: Draft the informal structure of the proof (Step 1, Step 2, ...) and map each to a Lean goal.
2.  **Gap Identification**: If a state-transition feels too large, create an intermediate helper lemma (`have` or `suffices`) to bridge the gap.
3.  **Tactic-State Interaction**: Use the `terminal` to run `lake build` after each state-transition to verify the goal state.
4.  **Proof Term Density**: Once the chain is closed, refactor the tactics into dense proof terms (using `exact`, `calc`, or term-mode) as mandated by the Constitution.

## Tools
- `terminal`: To interact with the Lean compiler.
- `trace_and_retrieve.py`: To find proofs for intermediate states.
