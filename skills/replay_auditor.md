# Skill: Replay Auditor

> **"The Reviewer is the Adversary of the Mediocre. Rubedo is the Furnace."**

## Objective
Verify the integrity of a proposed proof patch against the **Proof-Orchestration Constitution** and the **Agentic Soul** doctrine.

## Guidelines
1.  **Rubedo (Compiler Closure)**:
    - **Gate 1**: Run `lake build` and verify zero errors.
    - **Gate 2**: Run `tools/infra/semantic_audit.py` and verify zero drift in theorem identity.
    - **Gate 3**: Verify path application in the `quarantine/` directory using `verify_replay.sh`.
2.  **The Furnace of Invariants**: Check for accidental introduction of axiomatic leakage (e.g., `sorry`, `axiom`). Verify that ONLY the invariant mathematical law survives the build process.
3.  **Shadow Quarantine**: If a proof fails any gate, return it to the **Residue (Shadow Quarantine)**. No symbol reaches the repository main branch unless it is fully crystallized.

## Tools
- `tools/infra/semantic_audit.py`: The primary audit sieve.
- `lake`: The Lean build system.
- `git diff`: To monitor side-effects.
