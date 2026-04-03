---
name: lean-canonicalization-policy
description: Use when editing canonical Lean files in this repository and you need to preserve owner order, adjacent translation layers, real bridge theorems, and low public theorem burden.
---

# Lean Canonicalization Policy

Use this skill for theorem ownership, file splitting, wrapper elimination, bridge hygiene, and graph-guided refactors in this repository.

If the task is repo-wide, also read `skills/info-geometry-repo/SKILL.md`.

Canonicalization in this repo is morphism-first, not flattening-first.
The goal is to keep the public owner surface honest while preserving valid mathematics across noncanonical and exploratory surfaces.

## Core Classification

Every stable file should be classified as one of:
- owner
- translator
- coherence file
- capstone consumer

Every public declaration should be classified as one of:
- constructive endpoint
- lower bridge identification
- transport lemma
- wrapper or projection surface
- packaging scaffold
- capstone consumer theorem

If a file mixes several roles, split by ownership instead of keeping a mixed facade.
Do not erase a mathematically meaningful noncanonical presentation just because it is not yet stable.
Quarantine, demote, or rebuild it honestly.

## Adjacency Rule

The stable spine uses the native `RepDepth` semantic taxonomy (defined as an inductive
type in `Architecture.lean`). Tags are `@[rep_depth <level>]`.
Primitive translators should only move one adjacent step:
- `count` → `projective`
- `projective` → `operator`
- `operator` → `krein`
- `krein` → `transport`
- `transport` → `thermo`

The first enforcement layer is Lean-native:
- `lean/InfoGeometry/Meta/Architecture.lean`
- `lean/InfoGeometry/Audit.lean`

If a file introduces new ontology and skips a layer, it is debt.
Multi-layer files are only acceptable as coherence files or capstones.
The point of cleanup is to make adjacent transports explicit, not to deny that the theory has several legitimate representation levels.

## Mandatory Theorem Burden

A new public theorem in a canonical owner file is forbidden unless it survives all three tests:
1. deletion test: deleting it and unfolding definitions loses mathematics, not convenience
2. downstream test: a stronger downstream theorem actually uses it
3. non-definitional test: it is not `rfl`, `Iff.rfl`, a one-step `simp`/`simpa`, or unfold-and-rename

If it fails, keep it private, local, or as interpretation vocabulary.
If the underlying idea is mathematically meaningful but unfinished, move it to a noncanonical or quarantine surface instead of pretending it is canonical proof.

Every new public theorem in a canonical owner file should carry a `-- theorem-class: ...` tag immediately above it.

## Structural Rules

1. definitions live at the lowest natural owner
2. umbrella files import and re-export; they do not own mathematics
3. public theorems must be mathematically load-bearing
4. projection and pass-through wrappers belong behind the owner or in a Rosetta layer
5. do not invent a parallel ontology when a lower substrate already exists
6. preserve theorem names when splitting by moving the owner, not renaming the math
7. theorem count is not progress; stronger invariants and lower witness burden are progress

## Default Workflow

1. read the target file and its direct consumers
2. classify each declaration by role
3. remove proposition aliases and fake theoremification first
4. split mixed files into owner / translator / coherence / capstone layers
5. narrow imports in direct consumers
6. run `python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit` once tagged surfaces are in play
7. build the new owners and the obvious consumers
8. only after code is stable, run the DAG pipeline

When context is weak, re-read:
- `docs/OperationalIntent.md`
- `docs/Theory.md`
- the specific owner files that actually carry the morphisms

## Graph Use

Use graph tooling as a second pass only.
Before consulting any DAG artifact, verify `artifacts/dag/index/meta.json` timestamp is recent and `schemaVersion` ≥ 2.
Edge integrity is now enforced at export time via `validateEdges` — if artifacts exist, referential integrity holds.

- `theorem-surface-index` finds public theorem burden
- `semantic-quotient` separates shell from trunk
- `projection-coloring` is heuristic and can collapse after major cleanup
- `representation-depth-audit` should agree with the native Lean audit
- `representation-depth-graph` is a rendered presentation map, not the primary law
- `process-flow` artifacts are useful when deciding whether a declaration is real transport, local wrapper noise, or unresolved coherence pressure
- `meta.json` confirms artifact freshness, schema version, and build provenance (oleanHash)
