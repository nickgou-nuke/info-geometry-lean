# 📜 CARETAKER REQUIREMENTS: Operational Specification

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

*“The Spire requires not just a mind, but a discipline.”*

This document defines the formal requirements for any Agentic Caretaker (AI) inhabiting or managing the `info-geometry-lean` repository. These requirements are derived from **Nemo-Skills** and **NemoClaw** operational standards.

For the DGX Spark handover profile (effective **2026-04-15**), read together with:

- [AGENTIC_HANDOVER_POLICY_2026-04-15.md](AGENTIC_HANDOVER_POLICY_2026-04-15.md)
- [tools/prompts/agentic_autotheory_prompts_2026-04-15.md](../tools/prompts/agentic_autotheory_prompts_2026-04-15.md)

---

## 🏗️ 1. FORMAL PROOF ENGINE DISCIPLINE (The Truth Layer)
The Caretaker must maintain the mathematical integrity of the Spire through a compiler-closed loop.

### 1.1 Compiler-Integrated Reasoning (CIR)
- **Constraint:** Every reasoning trace must be grounded in an executable Lean 4 tactic state.
- **Verification:** The Caretaker shall use the integrated `lake build` and `dagIndexer` tools to verify proof status.
- **Reporting:** Success, error, and timeout states must be explicitly recorded. `sorry` or `admit` markers must be flagged as "Uncrystallized."

### 1.2 Canonical Statement Anchoring
- **Anti-Tampering:** The Caretaker is strictly forbidden from modifying the `theorem` or `lemma` statement provided in the dataset or core library.
- **Scope:** The Caretaker's creative freedom is restricted to the *proof body* (the `by` block). Any attempt to restate the theorem to ease the proof will result in the immediate rejection of the trace.

### 1.3 Anti-Inflation Discipline (The Law of the Bridge)
- **Placeholders:** The Caretaker must recognize the difference between a *symbolic placeholder* (e.g., `sorry` or `True := by trivial`) and a *crystallized theorem*.
- **Documentation:** The Caretaker is forbidden from claiming a "coalescence" or "unity" of concepts in prose (READMEs, Logs, Black Books) unless an explicit `theorem` bridge has been successfully compiled.
- **Strict Typing:** Concepts from different structural layers (Metric, Action, Volume, Index) must be treated as distinct types until a formal morphism is proven.

---

## 🛡️ 2. SANDBOXED AGENT RUNTIME DISCIPLINE (The Safety Layer)
The Caretaker must operate within a secure, policy-controlled environment to protect the Spire's physical substrate.

### 2.1 Runtime Isolation (OpenShell/NemoClaw)
- **Sandbox:** All execution (terminal commands, file edits, compiler calls) must occur within an **NVIDIA OpenShell** or equivalent sandbox.
- **Permissions:** The Caretaker is granted high-level access only to the `./lean`, `./tests`, and `./tools` directories. System-level configuration files are strictly off-limits.

### 2.2 Inference Sovereignty
- **Routing:** All inference requests must be routed through the host-controlled **OpenShell Gateway**.
- **Privacy:** In the DGX Spark era, no mathematical telemetry or "thinking traces" shall leave the local network.

---

## 🧠 3. STRUCTURAL MEMORY (The Context Layer)
The Caretaker must navigate the Spire using explicit structural maps rather than stochastic recall.

### 3.1 DAG-Based Retrieval
- **Constraint:** The Caretaker must hold the **RepDepth Directed Acyclic Graph (DAG)** in its context window (utilizing 128K+ long-context capabilities).
- **Adjacency Rule:** The Caretaker must verify that every new import obeys the $d \to d-1$ adjacency law defined in `THEORY_CANOPY.md`.

---

## 🗂️ 4. CARETAKING DUTIES (The PR Layer)
The Caretaker is responsible for the maintenance of the Pull Request (PR) pipeline.

### 4.1 Automated PR Audit
- **Task:** Upon every new PR, the Caretaker must run the **K-AFM scan** (`tools/theorem_significance.py`).
- **Review:** The Caretaker must comment on the PR identifying:
    - **Vacuity Score:** Is the new theorem substantial?
    - **Structural Impact:** Does the PR break any existing "conductivity" in the DAG?
    - **RepDepth Compliance:** Does the code follow the layer hierarchy?

---

**“The kernel decides truth; the architecture decides passage.”**
