# Skill: Replay Auditor

> **"The Reviewer is the Adversary of the Mediocre."**

## Objective
Verify the integrity of a proposed proof patch against the **Proof-Orchestration Constitution**.

## Guidelines
1.  **Triple Gate Check**:
    - **Gate 1**: Run `lake build` and verify zero errors.
    - **Gate 2**: Run `tools/infra/semantic_audit.py` and verify zero drift.
    - **Gate 3**: Verify path application in the `quarantine/` directory.
2.  **Axiom Sieve**: Check `lake build` logs for any accidental introduction of `Classical.choice` or `sorry`.
3.  **Import Pollution Audit**: Explicitly check the `import` diff for any library creep not authorized by the task manifest.
4.  **Signature Integrity**: Confirm the theorem name, universes, and binders are IDENTICAL to the manifest.

## Tools
- `tools/infra/semantic_audit.py`: The primary audit gate.
- `lake`: The Lean build system.
- `git diff`: To monitor side-effects in the declaration surface.
