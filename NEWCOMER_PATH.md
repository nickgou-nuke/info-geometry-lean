# Newcomer Path

This is the shortest reliable entry path into the repository.

## Step 1: understand the repo split

Read:
1. [README.md](README.md)
2. [docs/ModuleMap.md](docs/ModuleMap.md)
3. [Installation.md](Installation.md)
4. [docs/README.md](docs/README.md)

The repository is both:
- a Lean theorem library;
- a graph/audit toolchain for that library.

Before opening broad umbrella files, keep these roles straight:
- `lean/InfoGeometry.lean`: published library entrypoint
- `lean/InfoGeometry/Library.lean`: stable, linted canonical publication surface
- `lean/InfoGeometry/Canonical/All.lean`: stable canonical umbrella
- `lean/InfoGeometry/All.lean`: full project umbrella
- `lean/InfoGeometry/Audit.lean`: architecture audit entrypoint

## Step 2: learn the maintained entrypoints

Read:
1. [lean/DAG/README.md](lean/DAG/README.md)
2. [tools/README.md](tools/README.md)
3. [tools/infra/README.md](tools/infra/README.md)

## Step 3: build something small

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

If that works, build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

## Step 4: know what to ignore at first

Do not start with:
- `reports/`
- `archive/`
- conceptual notes under `docs/` as sources of live repo state
- stale generated counts embedded in old markdown files

The spine taxonomy is a semantic type (`count`, `projective`, `operator`, `krein`,
`transport`, `thermo`), not the old numeric L0–L5 system. If you see L0–L5 labels in
any doc, the semantic names from `Architecture.lean` are authoritative.

These are useful later, but not as the first source of truth.

If you want one concrete file chain before exploring a subtree, follow the
anchor corridor from [docs/ModuleMap.md](docs/ModuleMap.md):
`PositiveMeasure.lean -> Projective/Normalize.lean -> Canonical/PositiveRayCore.lean ->
Canonical/RelativePotentialCore.lean -> Canonical/RelativePotentialCountBridge.lean ->
Canonical/RelativeSurprisalOperatorLift.lean`.

## Step 5: when editing code

Use this order:
1. direct file analysis;
2. read direct consumers;
3. build the affected modules;
4. only then use graph reports;
5. only after code is stable, rerun the maintained DAG pipeline.

## Step 6: when using agents

Start with:
- [skills/info-geometry-repo/SKILL.md](skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](skills/lean-canonicalization-policy/SKILL.md)

The second skill encodes the current canonicalization discipline: split by ownership, keep public surfaces non-vacuous, and treat graph reports as second-pass guidance rather than first-pass truth.
