# Skill: Source Packetizer

> **"Structure precedes Formalization."**

## Objective
Convert unstructured mathematical source material (PDFs, notes, textbooks) into a structured JSON **Theorem Packet**.

## Guidelines
1.  **Extraction**: Read the provided source material and extract the core assertion, assumptions, and proof-sketch.
2.  **Structuring**: Generate a JSON packet with the following schema:
    ```json
    {
      "theoremName": "...",
      "provenance": "...",
      "context": "...",
      "informalGoal": "...",
      "informalSketch": "..."
    }
    ```
3.  **Provenance Integrity**: Ensure every packet contains a link back to the exact source (e.g., "Ref: [Book Title], Section 4.2").
4.  **Goal Isolation**: Separate the Informal Goal (English/LaTeX) from the Informal Sketch. Do not attempt to formalize the Lean signature in this stage.

## Tools
- `read_file`: Use to consume `docs/black_books/` or other raw material.
- `cat`: Use to combine notes.
