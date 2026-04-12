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
