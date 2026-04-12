# Skill: Statement Compiler

> **"A compiling signature is the first Victory of Unity."**

## Objective
Generate and repair Lean 4 declaration signatures (headers) based on a **Theorem Packet**.

## Guidelines
1.  **Drafting**: Convert the `informalGoal` from the Source Packet into a formal Lean 4 `theorem` or `def` header.
2.  **Signature Repair**: Run `lake build` or use the `LeanInteract` REPL to verify the signature. 
    - Fix universe parameters, binders, and missing imports.
    - DO NOT write the proof-body yet; use `sorry` or `constant` for the body during this stage.
3.  **Namespace Alignment**: Ensure the declaration is placed within the correctly qualified Spire namespace (e.g., `InfoGeometry.Canonical.Drazin`).
4.  **Audit Lock**: Once the signature compiles, freeze it. No further changes to the header are allowed during the formalization loop.

## Tools
- `LeanInteract`: To verify signature compilation.
- `lake`: For full-project build verification.
