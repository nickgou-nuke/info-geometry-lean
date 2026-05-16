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
