# Skill: Source Packetizer

> **"Structure precedes Formalization."**

## Objective
Convert unstructured mathematical source material (PDFs, notes, textbooks) into a structured JSON **Theorem Packet**.

## Guidelines
1.  **Extraction**: Read the provided source material and extract the core assertion, assumptions, and proof-sketch.
2.  **Structuring**: Generate a JSON packet according to the `docs/policy/packet_schemas.md` definition. This packet is the **Legislative Contract** for the formalization. The Proposer acts as the **Packet Producer**, while the Formalizer acts as the **Packet Consumer**.
3.  **Provenance Integrity**: Ensure every packet contains a link back to the exact source (e.g., "Ref: [Book Title], Section 4.2").
4.  **Goal Isolation**: Separate the Informal Goal (English/LaTeX) from the Informal Sketch. Do not attempt to formalize the Lean signature in this stage.
5.  **Packet Consumption**: Treat the `PremisePacket` as the **Absolute Fact Substrate**. Hallucinating premises outside this packet is a violation of the Soul.
6.  **Gap Identification**: If a state-transition feels too large, create an intermediate helper lemma (`have` or `suffices`) to bridge the gap.
7.  **Tactic-State Interaction**: Use the `terminal` to run `lake build` after each state-transition to verify the goal state.

## Handshake
Produce a `ChainOfStates` JSON object.

## Tools
- `read_file`: Use to consume `docs/black_books/` or other raw material.
- `cat`: Use to combine notes.
