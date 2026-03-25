# Newcomer Path

This is the shortest reliable entry path into the repository.

## Step 1: understand the repo split

Read:
1. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
2. [Installation.md](/home/goutev/LEAN4/info-geometry-lean/Installation.md)
3. [docs/README.md](/home/goutev/LEAN4/info-geometry-lean/docs/README.md)

The repository is both:
- a Lean theorem library;
- a graph/audit toolchain for that library.

## Step 2: learn the maintained entrypoints

Read:
1. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
2. [tools/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/README.md)
3. [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md)

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

These are useful later, but not as the first source of truth.

## Step 5: when editing code

Use this order:
1. direct file analysis;
2. read direct consumers;
3. build the affected modules;
4. only then use graph reports;
5. only after code is stable, rerun the maintained DAG pipeline.

## Step 6: when using agents

Start with:
- [skills/info-geometry-repo/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md)

The second skill encodes the current canonicalization discipline: split by ownership, keep public surfaces honest, and treat graph reports as second-pass guidance rather than first-pass truth.
