# Skills

Agent skill definitions for this repository.

## Repo-Specific Skills

| Skill | Purpose |
|-------|---------|
| [info-geometry-repo](info-geometry-repo/SKILL.md) | Primary repo skill: trust order, DAG pipeline, LeanTrail adapters/conformance, Arango ingest + physics eval, failure memory + path lock lanes, artifact inventory, default workflow |
| [repo-topic-deep-research](repo-topic-deep-research/SKILL.md) | Topic-agnostic deep repo investigation with status matrix (`implemented/interface/missing`) and agent context-pack generation |
| [lean-canonicalization-policy](lean-canonicalization-policy/SKILL.md) | Theorem ownership, file splitting, graph-guided refactors |
| [frontier-proof-compression](frontier-proof-compression/SKILL.md) | Skynet/OpenClaw proof compression and structural debt burn-down |
| [lean-sandbox](lean-sandbox/SKILL.md) | Mandatory sandbox-first development for safe repo integration |

## Generic Lean/Mathlib Skills

These are shared with `.agents/workflows/` (Copilot agent discovery surface):

| Skill | Purpose |
|-------|---------|
| [lean4](lean4/SKILL.md) | Core Lean 4 theorem proving, tactic reference, proof workflows |
| [lean-proof](lean-proof/SKILL.md) | One-step-at-a-time methodology, error priority, proof cleanup |
| [lean-setup](lean-setup/SKILL.md) | Repository clone, build, and toolchain setup |
| [lean-bisect](lean-bisect/SKILL.md) | Toolchain version bisection for regressions |
| [lean-mwe](lean-mwe/SKILL.md) | Minimal working examples for bug reports |
| [lean-pr](lean-pr/SKILL.md) | Lean 4 PR conventions |
| [mathlib-build](mathlib-build/SKILL.md) | Mathlib build and cache workflow |
| [mathlib-pr](mathlib-pr/SKILL.md) | Mathlib PR conventions |
| [mathlib-review](mathlib-review/SKILL.md) | Mathlib PR review guidelines |
| [nightly-testing](nightly-testing/SKILL.md) | Lean/Mathlib nightly testing infrastructure |

## Hidden Surface

`.agents/workflows/` is the Copilot agent discovery directory.
It contains one additional file not present here:

- [`.agents/workflows/formalization.md`](../.agents/workflows/formalization.md) — Copilot workflow entry point for the [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)

> **Note:** The 10 generic Lean/Mathlib skill directories exist as full copies in both
> `skills/` and `.agents/workflows/`. If they drift, `skills/` is authoritative.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md) for the current build/audit state.

## Style Guardrail

Repository-wide theorem-surface policy now enforces genuine witness dependency:

- avoid linter-masking existential wrappers like `∃ h : P, (let _ := h; Q)` for non-dependent `Q`
- prefer `∃ _ : P, Q` for non-dependent existence
- keep named witnesses only when they are semantically used downstream
- apply `PAULI_MANDATE` gate I–XI (including anti-existential-hypothesis, interface witness fidelity, metric fidelity, anti-residual-redirect, parameter-admission, and public-uniqueness)
