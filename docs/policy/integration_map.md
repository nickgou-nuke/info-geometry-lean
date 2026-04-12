# Spire Toolchain Integration Map (Corrigenda)

This document defines the **Crystalline Toolchain** for the Info-Geometry Spire, mapping the repository's orchestration loop to the specific state-of-the-art instruments of the Lean 4 ecosystem.

## ⚖️ The Hardened Shortlist

| Orchestration Stage | Instrument | Worldview |
| :--- | :--- | :--- |
| **I. Statement Compiler** | `siddhartha-gadgil/LeanAide` | Text/LaTeX to Lean skeleton autoformalization. |
| **II. Proof Substrate** | `lean-dojo/LeanDojo-v2` | Global repo tracing, premise extraction, and gym-like interaction. |
| **III. Tactic-Level Formalizer** | `lean-dojo/LeanCopilot` | In-Lean proof search (search_proof) and premise selection (select_premises). |
| **IV. Reference Corpus** | `optpku/ReasBook` | Primary reference-preserving formalization corpus. |
| **V. Retrieval/Style Corpus** | `teorth/analysis` | Large analysis corpus for style and retrieval, but not a fully-closed gold truth. |

## 🛠️ The Hardened Handover Chain

1.  **Input Text (LaTeX/Notes)**: Raw mathematical intent.
2.  **LeanAide Skeleton**: Autoformalization of the theorem/definition header.
3.  **Manifest Lock**: Legislative freeze of the signature.
4.  **LeanDojo-v2 Trace**: Extraction of the commit-indexed premise packet.
5.  **Formalizer Loop (LeanCopilot)**: State-level proof search and tactical refinement inside Lean.
6.  **Semantic Audit**: Binary verification of signature stability.
7.  **Replay Success**: Successful build in a fresh environment.

## 📈 Operational Priorities

### 1. ReasBook as Sovereign Corpus
While `teorth/analysis` is a valuable companion, **ReasBook** is the primary model for our architecture. It provides the necessary "Reference-Preserving" structure required for the Handover.

### 2. LeanDojo-v2 Interaction
All repository tracing must target the **LeanDojo-v2** architecture. The Spire's `trace_and_retrieve.py` serves as the lightweight local indexer, compliant with the V2 premise-extraction methodology.

### 3. LeanCopilot as Tactic Hand
The formalizer subagent shall prioritize **LeanCopilot** interfaces (`search_proof`) for closing theorem bodies, ensuring that tactical generation is conditioned on local state and premise retrieval.

---

**"Borrow the machine; keep the soul. ReasBook is the map; LeanDojo-v2 is the engine."**
