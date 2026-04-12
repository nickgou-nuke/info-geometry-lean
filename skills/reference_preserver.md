# Skill: Reference Preserver

> **"Provenance is the anchor of the Spire."**

## Objective
Preserve the structural integrity and documentation provenance of mathematical source material during formalization.

## Guidelines
1.  **Anchoring**: Always anchor a theorem or definition to its original source location (e.g., Chapter, Section, Page Number) in the docstring.
2.  **Naming Discipline**: Adopt names that reflect the reference source (e.g., `riesz_decomposition_Thm31`) as helper aliases if the canonical name is too abstract.
3.  **Structure Mirroring**: If a textbook organizes a proof into three distinct "Steps," the Lean formalization should reflect these steps as separate lemmas or structured sub-goals.
4.  **No Semantic Smoothing**: Do not "fix" the math of the reference unless it is a clear typo. Formalize the source as it exists.

## Tools
- `read_file`: Use to inspect `docs/black_books/` for provenance data.
- `ls`: Use to navigate the repository's reference structure.
