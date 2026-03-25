---
name: lean-canonicalization-policy
description: "Use when editing Lean 4 code in this repository and you need to preserve canonical structure: split overloaded files, keep theorem ownership low, reject wrapper-heavy public surfaces, classify declarations semantically, and use semantic quotient / projection-coloring reports only after direct file analysis."
---

# Lean Canonicalization Policy

Use this skill for Lean refactors that affect theorem organization, public API honesty, file ownership, or graph-driven module splitting in this repo.

If the task is repo-specific, also read `/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md`.
If the task is proof-focused, also read `/home/goutev/LEAN4/info-geometry-lean/skills/lean4/SKILL.md`.

## First Pass

Start with direct file analysis, not graph reports.

For each declaration classify it as exactly one of:
- constructive endpoint
- lower bridge identification
- transport lemma
- orientation / projection / unpacking wrapper
- existential or packaging scaffold
- capstone consumer theorem

If a file mixes multiple roles, split by ownership rather than deleting math.

## Structural Rules

1. Definitions live at the lowest natural owner.
2. Umbrella files import and re-export; they do not own mathematics.
3. Public theorems must be proof-bearing endpoints or real lower bridge identifications.
4. Projection, orientation, conjunction, and pass-through wrappers should be `private` or moved behind the owner file.
5. Strict-positive pointwise layers must stay separate from wide AE/support-hypothesis layers.
6. Never invent a parallel ontology when an existing lower substrate already exists.
7. Preserve theorem names when splitting by keeping the original namespace on the new owner files.

## Default Workflow

1. Read the target file and its direct consumers.
2. Classify declarations semantically.
3. Split mixed files into substrate / bridge / representation / capstone layers.
4. Narrow imports in direct consumers.
5. Build the new owner files and the obvious consumers.
6. Only after the code is stable, run the maintained DAG pipeline.
7. Use semantic quotient and projection coloring to decide the next split, not the current one.

## Graph Use

Use graph tooling as a second pass only.

- `semantic-quotient` tells you whether a hotspot is shell or trunk.
- `projection-coloring` tells you whether an upper file is monochrome over one lower cluster or genuinely braided.
- Split monochrome shells by lower-cluster ownership.
- Do not split braided files blindly.

Read `references/policy.md` for the full repo policy and mathlib-derived norms.
