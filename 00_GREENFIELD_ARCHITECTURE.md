# 🏰 THE GREENFIELD ARCHITECTURE (Info-Geometry Spire)

*Authored: 2026-05-02*
*Synthesis of Hermes (12-Point Plan) and the Native Caretaker Blueprint.*

This document defines the target "Level 3" execution state. It moves the repository from a collection of useful scripts into a hardened, industrial-grade formalization engine.

## 1. Unified Run Identity & Persistence
*   **Doctrine:** Every execution of any pipeline stage MUST carry a `run_id`.
*   **Format:** `run_{ISO8601_COMPACT}_{GIT_SHA_SHORT}_{UUID_SHORT}`.
*   **Invariance:** The `run_id` is generated once at the orchestrator entrypoint and propagated through environment variables to all sub-processes (Lean, Python, Arango).
*   **Memory:** All artifacts, logs, and Arango documents are correlated via this `run_id`.

## 2. The Pipeline Kernel (`ig-orchestrator`)
*   **Structure:** Replace scattered `.py` and `.sh` scripts with a central CLI tool.
*   **Subcommands:**
    *   `ig build`: Coordinates Lake and incremental artifact caching.
    *   `ig extract`: Runs Lean metaprograms to produce raw JSONL.
    *   `ig process`: Computes patches, spectral signatures, and fingerprints.
    *   `ig ingest`: Atomic upsert into ArangoDB with schema validation.
    *   `ig audit`: Runs Pauli compliance and Wilson-loop checks.
*   **Implementation:** Python library in `core/pipeline/` with a `tools/ig.py` entrypoint.

## 3. Strict Schema Contracts
*   **Doctrine:** No data enters ArangoDB without passing a JSON Schema validator.
*   **Location:** Schemas reside in `configs/schemas/` as the single source of truth for data shapes.
*   **Versioning:** Every schema has a `schema_version` field. Breaking changes require a migration script in `migrations/`.

## 4. Layered Separation of Lanes
*   **The Formal Lane (Truth):** Lean 4 Kernel. Sovereign and immutable.
*   **The Provenance Lane (Memory):** ArangoDB. Derived metrics, navigation, and agentic history.
*   **The Generative Lane (Proposal):** LLM/Inference. Non-authoritative, gated by the Pauli Auditor.
*   **Constraint:** No generative material may be labeled as `verified` without a "Proof-Carrying Link" to a kernel-discharged Lean theorem.

## 5. Geometric Knowledge Graph (Level 3 DEC)
*   **Metrics:** Graph edges carry physical attributes: `action_weight`, `affinity`, `chiral_phase`.
*   **Adjointness:** Implement weighted Hodge adjoints ($δ = M^{-1} d^T M$) for thermodynamically correct path reversal.
*   **Holonomy:** Wilson loops are standard audits for semantic drift across the Multilingual Bridge.

## 6. Reproducible Sovereignty (NemoClaw)
*   **Environment:** One blessed Python virtual environment with hard-pinned dependencies.
*   **Locality:** All inference is local via NIM (`localhost:8000`). No external telemetry.
*   **Sandbox:** All agentic edits happen in a `nemoclaw onboard` temporary workspace before PR promotion.

## Rollout Strategy
1.  **Stage A (Compatibility):** Introduce the `run_id` and the orchestrator wrapper around existing scripts.
2.  **Stage B (Hardening):** Enable schema validation on all `ig ingest` calls.
3.  **Stage C (Refactoring):** Move script logic into the `core/` library and delete root-level sprawl.
