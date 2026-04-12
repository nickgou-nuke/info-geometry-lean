# Skill: Formalizer Loop

> **"Iterate until closure. Repair until audit."**

## Objective
Implement an iterative proof-generation and repair loop using the `LeanInteract` REPL bridge.

## Guidelines
1.  **Goal Retrieval**: Use the `get_proof_state` tool to extract the current Lean goal.
2.  **Tactic Iteration**: Propose a tactic based on the goal and the **Premise Packet**.
3.  **REPL Feedback**: Execute the tactic via `apply_tactic`. 
    - If successful, move to the next state in the **Chain of States**.
    - If failure, analyze the error message and propose a **Repair Tactic**.
4.  **Audit Awareness**: Constant checking for `sorry` or axiomatic leakage. No step is final until the goal state is `No goals`.
5.  **Refactoring**: Once the goal is closed, use the full proof history to refactor into a dense, crystalline proof term as defined by the Constitution.

## Tools
- `tools/infra/lean_interact_wrapper.py`: The REPL bridge.
- `skills/premise_retriever`: To fetch new facts for repair.
