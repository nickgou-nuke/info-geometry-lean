---
name: opengauss_commands
description: >-
  Provides the 9 native OpenGauss capabilities (/prove, /golf, /refactor, /autoformalize, etc.)
  directly into the Antigravity context, powered by the lean-lsp-mcp backend.
---

# OpenGauss Native Workflows

This skill natively integrates the OpenGauss mathematical theorem orchestration system into your agent.

When the user requests an OpenGauss workflow (e.g. "Run /prove on X"), you must act as the requested OpenGauss subagent, utilizing your `lean-lsp-mcp` tools to accomplish the task exactly as the original `gauss_cli` Python logic would.

## 1. `/prove` (Guided Prover)
- **Role**: Interactive cycle-by-cycle proof engine.
- **Workflow**: Check theorems via LSP, identify `sorry` bounds, write small helper lemmas, verify via `lake env`.

## 2. `/draft` (Skeleton Drafter)
- **Role**: Converts informal math into Lean declaration skeletons with `sorry`.

## 3. `/review` (Read-Only Auditor)
- **Role**: Non-destructive code, axiom, and proof quality review.

## 4. `/checkpoint` (State Saver)
- **Role**: Saves state into a verified checkpoint after compiling and checking axioms.

## 5. `/refactor` (Proof Refactorer)
- **Role**: Extracts reusable named lemmas, simplifies monolithic proofs.

## 6. `/golf` (Proof Optimizer)
- **Role**: Compresses proofs, replacing slow `simp` or `native_decide` tactics with terms/`rfl`.

## 7. `/autoprove` (Autonomous Prover)
- **Role**: Unattended multi-cycle proof engine.

## 8. `/formalize` (Interactive Synthesis)
- **Role**: Two-phase workflow (drafting + guided proving) requiring user interaction.

## 9. `/autoformalize` (Autonomous Formalization)
- **Role**: End-to-end translation of CAS/informal text into fully verified Lean code.

*You now possess 1-to-1 operational equivalence with OpenGauss.*
