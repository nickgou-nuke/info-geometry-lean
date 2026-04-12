# Skill: Source Packetizer

> **"Structure precedes Formalization. Skeletons precede Proofs."**

## Objective
Convert unstructured mathematical source material (Black Books, notes, textbooks) into a structured JSON **Theorem Packet** and a compiled Lean signature.

## Guidelines
1.  **Nigredo (Alchemical Discovery)**: Admit raw conceptual pressure and imagery from the Black Books. This stage is ore, not mathematics.
2.  **Albedo (Clinical Purge)**: Translate symbolic discovery into an exact formal signature (Definition, Theorem, or Dependency). Verify that every symbol is mapped to a formal candidate.
3.  **Purge of Lyrical Overfit**: Remove expressive names that lack definitional content. Ensure the signature is crystalline.
4.  **Structuring**: Generate a JSON packet according to the `docs/policy/packet_schemas.md` definition. This packet is the **Legislative Contract** for the formalization.
5.  **Signature Lock**: Verify that the generated skeleton compiles (with `sorry` body) before closing the Phase.

## Handshake
Produce a `ChainOfStates` JSON object and a frozen theorem signature.

## Tools
- `read_file`: Use to consume `docs/black_books/` or other raw material.
- `lake`: Use to verify signature compilation.
