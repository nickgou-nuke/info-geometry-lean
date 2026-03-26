---
name: lean-canonicalization-policy
description: "Use when editing Lean 4 code in this repository and you need to preserve canonical structure: split overloaded files, keep theorem ownership low, reject wrapper-heavy public surfaces, reject fake theoremification, classify declarations semantically, and use theorem-surface / semantic-quotient / projection-coloring reports only after direct file analysis."
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

## Mandatory Theorem Burden

A new public theorem in a canonical owner file is forbidden unless it survives all three tests:
1. deletion test: deleting it and unfolding definitions must lose mathematics, not just convenience
2. downstream dependence test: a mathematically stronger downstream theorem must use it
3. non-definitional proof test: it must not be `rfl`, `Iff.rfl`, one-step `simp`/`simpa`, or unfold-and-rename

If it fails any test, keep it as `abbrev`, private/local lemma, or interpretation vocabulary.

Every new public theorem in a canonical owner file must also be preceded immediately by a tag like `-- theorem-class: bridge`.

## Structural Rules

1. Definitions live at the lowest natural owner.
2. Umbrella files import and re-export; they do not own mathematics.
3. Public theorems must be mathematically load-bearing, not proposition renamings.
4. Projection, orientation, conjunction, and pass-through wrappers should be `private` or moved behind the owner file.
5. Strict-positive pointwise layers must stay separate from wide AE/support-hypothesis layers.
6. Never invent a parallel ontology when an existing lower substrate already exists.
7. Preserve theorem names when splitting by keeping the original namespace on the new owner files.
8. Theorem count is not progress. Only reduced witness burden, stronger invariants, and real bridge closure count.

## Default Workflow

1. Read the target file and its direct consumers.
2. Classify declarations semantically.
3. Remove proposition aliases and fake theoremification before splitting larger ownership blocks.
4. Split mixed files into substrate / bridge / representation / capstone layers.
5. Narrow imports in direct consumers.
6. Build the new owner files and the obvious consumers.
7. Only after the code is stable, run the maintained DAG pipeline.
8. Use theorem-surface audit, semantic quotient, and projection coloring to decide the next split, not the current one.

## Graph Use

Use graph tooling as a second pass only.

- `theorem-surface-index` tells you where theorem surface has become vacuous, package-like, or bridge-thin.
- `semantic-quotient` tells you whether a hotspot is shell or trunk.
- `projection-coloring` tells you whether an upper file is monochrome over one lower cluster or genuinely braided.
- Split monochrome shells by lower-cluster ownership.
- Do not split braided files blindly.

Read `references/policy.md` for the full repo policy and mathlib-derived norms.
