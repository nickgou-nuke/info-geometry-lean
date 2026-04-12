# Skill: State-Chain Formalizer

> **"Closure is a sequence of transformations, not a single leap. Citrinitas is the bridge."**

## Objective
Decompose complex formalization tasks into a **Chain of States** (informal steps mapped to formal targets) according to the Citrinitas methodology.

## Guidelines
1.  **Citrinitas (Symbolic Decomposition)**: Bridge the gap between intuition and Lean by drafting a JSON `ChainOfStates`. Map every informal pressure point to a formal target.
2.  **State Logic**: If a state-transition feels too large, create an intermediate helper lemma (`have` or `suffices`) to bridge the gap. No leap should be wider than a single tactical proof-step.
3.  **Premise Anchoring**: Treat the `PremisePacket` as the **Absolute Fact Substrate**. Retrieval-first reasoning is mandatory for every state transition. 
4.  **Interaction**: Use the `LeanInteract` REPL bridge to verify each state-transition in the chain.

## Handshake
Consume a `ChainOfStates` and produce a valid Lean tactic sequence.

## Tools
- `tools/infra/lean_interact_wrapper.py`: The REPL bridge.
- `tools/infra/trace_and_retrieve.py`: The premise engine.
