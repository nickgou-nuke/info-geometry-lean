---
name: lean-skill-library
description: Use when selecting, installing, or sequencing Lean 4 proof-automation skills for this repo; catalogs local skills and external GitHub skills for theorem proving, review, refactoring, visualization, and autoproofing workflows.
---

# Lean Skill Library

This skill is an index, not a proof workflow. Use it to pick the narrowest
skill set for a Lean task, or to decide whether an external skill should be
installed locally.

## Default ordering

0. `protected-baseline-formalization` as the operating identity for any repository-wide formalization request; its gate checklist overrides closure claims.
1. `lean4` for any Lean edit, build, or diagnostic work.
2. `lean-proof` for theorem proving and `sorry` filling.
3. `proof-only-mandate` for anti-cheat / no-wrapper policy enforcement.
4. `lean-mwe` for minimization and small reproducible examples.
5. `lean-bisect` for regressions and failing-build isolation.
6. `mathlib-build` and `mathlib-review` for build/review gates.
7. `paperproof-validator` for proof-state inspection.
8. `lean-dag-wire-refactor` for wrapper cleanup and duplicate theorem surfaces.
9. `categorical-infrastructure-projection` and `virasoro-finite-to-infinite-transition` for bridge work.
10. `sympy-lean-handoff` for exact symbolic verification followed by Lean 4 translation.
11. `mission-loop`, `closure-mission-loop`, and `closure-debt-proof` for repeated debt burn-down.

## External candidates

See [references/catalog.md](references/catalog.md) for the local index of
external public skills and Lean tooling repositories.
See [references/collected-skills.md](references/collected-skills.md) for the
capability map of the vendored Lean skill pack and related tooling.

## Use rules

- Keep Lean proof authority in Lean, not in the skill catalog.
- Prefer repo-local skills first.
- Install external skills only when the local stack lacks the capability.
- Update the catalog when a skill is added, removed, or promoted.
