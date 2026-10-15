---
name: opengauss_commands
description: >-
  Provides the extended OpenGauss / TeamAntigravity capabilities (15 commands: /prove, /check, /refute,
  /draft, /review, /checkpoint, /refactor, /golf, /autoprove, /formalize, /autoformalize, /handoff,
  /discover, /quarantine, /certify) directly into the Antigravity subagent context, powered by
  tools/infra/opengauss_cli.py, tools/infra/opengauss_screener.py, the 17-Trap Catalog, and the
  Assume-and-Recurse Top-Down Protocol.
---

# OpenGauss Native Workflows & TeamAntigravity Subagent Protocol

This skill integrates the local **TeamAntigravity extension** of [`math-inc/opengauss`](https://github.com/math-inc/opengauss) (`OpenGauss/`).

Whereas upstream `math-inc/opengauss` provides a TUI wrapper (`gauss`) and PTY `SwarmManager` over the **9 `cameronfreer/lean4-skills` commands** (`/prove`, `/draft`, `/review`, `/checkpoint`, `/refactor`, `/golf`, `/autoprove`, `/formalize`, `/autoformalize`), this repository extends the protocol to **15 native CLI commands** (`python3 tools/infra/opengauss_cli.py`), an **automated 17-Trap Static Screener** (`python3 tools/infra/opengauss_screener.py`), and a **3-Tier TeamAntigravity Subagent Swarm** (`invoke_subagent` / `define_subagent` / `send_message`) governed by:
- **Assume-and-Recurse Top-Down Protocol**: [`../../reference/TOP_DOWN_PROTOCOL.md`](../../reference/TOP_DOWN_PROTOCOL.md)
- **17-Trap Catalog (T1–T17)**: [`../../reference/TRAP_CATALOG.md`](../../reference/TRAP_CATALOG.md)
- **Extended Protocol Policy**: [`../../../../docs/policy/OPENGAUSS_PROTOCOL_EXTENSIONS.md`](../../../../docs/policy/OPENGAUSS_PROTOCOL_EXTENSIONS.md)

---

## Upstream `math-inc/opengauss` vs. Local TeamAntigravity Extension

| Dimension | Upstream `math-inc/opengauss` | Local TeamAntigravity Protocol |
|---|---|---|
| **Command Surface** | 9 `lean4-skills` slash commands (`/prove`, `/draft`, `/review`, `/checkpoint`, `/refactor`, `/golf`, `/autoprove`, `/formalize`, `/autoformalize`) + `/swarm` | **15 deterministic CLI + subagent commands** (adds `/discover`, `/check`, `/refute`, `/handoff`, `/quarantine`, `/certify`) |
| **Swarm Runtime** | `OpenGauss/swarm_manager.py` spawning background `claude --dangerously-skip-permissions` PTY sessions | Native **TeamAntigravity Subagents** (`invoke_subagent`) in a 3-Tier hierarchy (Leader → Orchestrator → Sandbox Worker Swarm) |
| **Write Isolation** | Child sessions mutate the active project root directly | **Subagent Sandbox Mandate**: subagents write strictly to `scratch/` or `proofs/` sandboxes; only the Orchestrator promotes verified diffs |
| **Adversarial Gate** | Read-only `/review` after drafting | Paired **Prover + Refuter** subagents + static **17-Trap Screener** (`T1–T17`) at Gate 2 & Gate 2.5 |
| **Failure Handling** | `trajectory_compressor.py` + shadow git rollback | **Pillar II Residue Quarantine** (`/quarantine`) emitting `TypedObstructionPacket` JSONs into `artifacts/residue_quarantine/` |
| **Build & Axiom Gate** | Uncoordinated `lake` calls inside child sessions | Single-flight `run_locked_lake_build.py --wait-for-build-lock` + companion `*Audit.lean` (`#print axioms` $\subseteq$ `[propext, Classical.choice, Quot.sound]`) |

---

## The 15 OpenGauss / TeamAntigravity Commands

### 1. `/prove` (Top-Down Assume-and-Recurse Prover)
- **Role**: Recursive top-down theorem decomposition engine (`opengauss_cli.py prove`).
- **Workflow**:
  1. Define headline theorem signature.
  2. Posit consumer-minimal helper lemmas (Anti-T11 Law).
  3. Compile the parent glue immediately (`by exact ...`).
  4. Dispatch sandboxed worker subagents (`Prover` paired with `Refuter`) to close leaf lemmas.
  5. Verify `#print axioms` consists strictly of `[propext, Classical.choice, Quot.sound]`.

### 2. `/check` (Ground-Truthed Counterexample Hunter & Consistency Auditor)
- **Role**: Discovers counterexamples, contradictory/vacuous hypotheses, $\exists\forall$ quantifier inversions (T2/T2′), and signature clashes (T13) before proofs are attempted (`opengauss_cli.py check`).

### 3. `/refute` (Adversarial False-as-Stated Screener — 17-Trap Catalog)
- **Role**: Adversarially screens Lean 4 files or directories against the **17 False-as-Stated Traps** (`opengauss_cli.py refute <paths> --strict`):
  - **T1**: Raw chart-coordinate extraction off-basepoint.
  - **T2/T2′**: Free-family quantifiers & $\exists\forall$ inversion.
  - **T3**: Global flatness / locally constant charts (`HasLocallyConstantChartAt`).
  - **T4**: Vacuous binders & degenerate hypotheses (`0 = 0`, `True`, `x = x`).
  - **T5**: Localized headline leaks.
  - **T6**: Hypothesis packaging (hypothesis identical to conclusion closed via `exact h`).
  - **T7**: Family-as-input vs. existential output.
  - **T8**: Per-fibre vs. joint continuity.
  - **T9**: Two-sided interval derivatives on cutoffs (`HasDerivAt` on `Icc`/`Ici`).
  - **T10**: $C^\infty$ at boundary over-demand.
  - **T11**: Over-strong / non-tensorial posits.
  - **T12**: Multi-conjunct $\exists$-freedom over-constraints.
  - **T13**: Metric signature & orientation clashes.
  - **T14**: Constant factor & dimension scaling mismatches.
  - **T15**: Definitional expansion loops (`dsimp`/`unfold` on `TensorTower`/`Colimit`/`Quotient`).
  - **T16**: Semantic Surrogate / Scalar Toy Proxy (4 sub-gates: scalar trace/det proxy structs, pre-commutator homomorphism collapse, carrier-matched non-commutativity witness requirement, and scalar tactic misuse `ring`/`linarith` on unprojected operators).
  - **T17**: Unwitnessed Structure / Model Non-Degeneracy Risk (Gate 2.5: every `structure`/`class` must have a closed constructive inhabitant or `Inhabited` instance untainted by `axiom`/`sorry` or ambient variables).

### 4. `/draft` (Skeleton Drafter)
- **Role**: Generates Lean 4 declaration skeletons with explicit leaf `sorry` lemmas and glued parent theorem (`opengauss_cli.py draft`).

### 5. `/review` (Independent QMS Read-Only Auditor)
- **Role**: Non-destructive static preflight audit under `QMS-SOP-IAA-001` (`opengauss_cli.py review <paths> --gate GATE_2|GATE_4`). Note: `GATE_4` static review reports `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` until paired with locked Lean compilation and `#print axioms` verification.

### 6. `/checkpoint` (State Saver & Continuous Tracker)
- **Role**: Records repository state and stages specified paths (`git add`) to protect work against loss (`opengauss_cli.py checkpoint`).

### 7. `/refactor` (Proof Refactorer & DAG Redundancy Cleaner)
- **Role**: Scans for monolithic proof blocks (>25 lines) violating the Lean File Size & Lemma Reuse Mandate and suggests helper extractions (`opengauss_cli.py refactor <path>`).

### 8. `/golf` (Proof Optimizer)
- **Role**: Scans for redundant tactic sequences (`simp; ring`, `by exact rfl`, `simp only [id]`) and suggests direct replacements (`opengauss_cli.py golf <path>`).

### 9. `/autoprove` (Autonomous Multi-Cycle Engine)
- **Role**: Tracks open `sorry` counts and dead routes across cycles (`opengauss_cli.py autoprove <target>`), automatically re-hydrating banned directions from `artifacts/residue_quarantine/`.

### 10. `/formalize` (Two-Phase Interactive Synthesis)
- **Role**: Aligns informal mathematical specifications with canonical categorical owners (`TensorTowerColimit`, `SolderingIsomorphism`, etc.) and screens for traps before synthesis (`opengauss_cli.py formalize --spec "..." --phase 1|2`).

### 11. `/autoformalize` (End-to-End CAS to Lean Candidate Translator)
- **Role**: Translates symbolic CAS identities (SymPy, Macaulay2, GAP) into candidate Lean 4 theorems (`opengauss_cli.py autoformalize --cas sympy --expr "..." --name "..."`).

### 12. `/handoff` (Cross-Session Context Preserver)
- **Role**: Serializes active targets, verified checkpoints, dead routes, and next actions into an M10 Anti-Compaction handoff markdown (`opengauss_cli.py handoff`).

### 13. `/discover` (Pre-Flight Declaration & Carrier Hunter — Gate 0)
- **Role**: Scans `lean/InfoGeometry/` and Mathlib for existing structures, classes, defs, and lemmas matching a query to prevent structural duplication (`opengauss_cli.py discover --query "..."`).

### 14. `/quarantine` (Rejected Route & Residue Obstruction Isolator — Pillar II)
- **Role**: Packages a refuted statement or trap violation into an immutable `TypedObstructionPacket` JSON in `artifacts/residue_quarantine/` (`opengauss_cli.py quarantine --file ... --trap ... --desc ... --counter ... --constraint ...`).

### 15. `/certify` (Companion Axiom Certification Script Generator — Pillar IV)
- **Role**: Extracts public theorem/lemma names with their active namespace scopes and emits a companion `#print axioms` script. `--verify-kernel` builds the owner and checks the audit under the shared build lock; without it, output is only a static script candidate.
- **CLI**: `certify --file FILE [--write-audit] [--verify-kernel] [--json]`.

---

*Equipped with 1-to-1 operational equivalence with upstream `math-inc/opengauss` plus the 6 TeamAntigravity adversarial, discovery, quarantine, and certification extensions.*
