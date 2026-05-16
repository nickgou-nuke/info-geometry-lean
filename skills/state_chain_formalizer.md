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
