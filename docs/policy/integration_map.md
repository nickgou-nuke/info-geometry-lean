# Spire Toolchain Integration Map

This document maps the **Spire Toolchain** to its technical predecessors in the Lean 4 ecosystem. It ensures that the handover architecture is anchored to proven methodologies while remaining governed by the Spire's **Proof-Orchestration Constitution**.

## ⚖️ The Borrowed Landscape

| Component | Borrowed From | Worldview |
| :--- | :--- | :--- |
| **Stage 1 & 2** | `optsuite/M2F` | Staged formalization (Signature first, Proof second). |
| **Stage 1** | `optpku/ReasBook` | Source discipline and reference-preserving structure. |
| **Stage 3** | `lean-dojo/LeanDojo` | Repository tracing and premise extraction. |
| **Stage 3** | `lean-dojo/ReProver` | Retrieval-augmented tactic generation. |
| **Stage 4** | `augustepoiroux/LeanInteract` | Pythonic REPL interaction for iterative repair loops. |
| **Stage 4** | `lean-dojo/LeanCopilot` | In-Lean proof search and tactic suggestion. |

## 🛠️ The Spire Integration Flow

### I. Reference Packetizer (`skills/source_packetizer.md`)
Inspired by the **ReasBook/M2F** approach to lit-driven formalization. It converts unstructured mathematical prose into a JSON-structured "Theorem Packet."

### II. Statement Compiler (`skills/statement_compiler.md`)
Implements the **M2F Stage-1** logic. It performs "Signature Repair" by using Lean compiler feedback to fix declaration skeletons before a single proof-step is written.

### III. Premise Retriever (`skills/premise_retriever.md`)
Leverages **LeanDojo-style** repository tracing via `tools/infra/trace_and_retrieve.py`. It fetches the specific "Bedrock Packet" required for the goal-state.

### IV. Formalizer Loop (`skills/formalizer_loop.md`)
Wraps the **LeanInteract** Python REPL. It implements a non-extensional repair loop: `Propose Tactic -> Execute via REPL -> Audit State -> Retry`.

### V. Constitutional Audit (`skills/replay_auditor.md`)
The Spire's unique gate. Enforces the **Triple Gate** (Build, Audit, Replay) on all outputs from the Formalizer Loop.

---

**"Borrow the machine; keep the soul."**
