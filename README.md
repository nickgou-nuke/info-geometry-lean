# InfoGeometry in Lean 4

`info-geometry-lean` is a Lean 4 repository with three maintained surfaces:
- a theorem library under `lean/InfoGeometry/`
- a Lean-native architecture kernel under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
- a graph and reporting toolchain under `lean/DAG/` and `tools/infra/`

The repo is best read as one theory with several presentations, not as many unrelated theories.
The main mathematical burden is not only in the objects at each layer, but in the morphisms that move between those layers and prove that adjacent presentations agree.
The current stable spine is organized by representation depth:
- `L0` Count: raw relative counts and positive-measure representatives
- `L1` Projective/Gauge: positive rays, normalization, relative log-potentials
- `L2` Operator: diagonal operator lift, partition and log-partition calculus
- `L3` Krein/Clifford: split quadratic geometry, polarized sheets, Dirac compatibility
- `L4` Transport: Bogoliubov and transported spectral/thermal structure
- `L5` Thermodynamic/Attention: Gibbs, Sinkhorn, softmax, and attention surfaces

A public bridge file is healthy only if it is either:
- an adjacent translator between neighboring depths
- a coherence file proving two adjacent composites agree

That grammar is now enforced in two places:
- natively in [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)
- as rendered reports in [reports/dag](/home/goutev/LEAN4/info-geometry-lean/reports/dag)

## Repository Intention

The repo should be read as one transport theory over several symmetric, projective, operator, Krein, and thermodynamic presentations.
`canonical` does not mean "the only true mathematics".
It means "the stable public owner surface".
Valid mathematics outside that surface should be developed, quarantined, or promoted honestly, not discarded because it is noncanonical.

The practical goal of formalization here is to make the morphisms explicit and checkable:
- owner files define the natural presentation-level objects
- translator files move one adjacent step in the representation ladder
- coherence files prove that two adjacent composites agree
- capstone files summarize lower mathematics without pretending to be foundational proof owners

The DAG and Python tooling exist to preserve this intention when local context is lost:
- they externalize dependency memory
- they surface owner/translator/coherence/capstone pressure
- they expose residual comparison debt and wrapper burden
- they do not legislate mathematical truth or replace code reading

The short operational summary lives in [docs/OperationalIntent.md](/home/goutev/LEAN4/info-geometry-lean/docs/OperationalIntent.md).

## Read First

1. [Installation.md](/home/goutev/LEAN4/info-geometry-lean/Installation.md)
2. [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md)
3. [docs/README.md](/home/goutev/LEAN4/info-geometry-lean/docs/README.md)
4. [docs/OperationalIntent.md](/home/goutev/LEAN4/info-geometry-lean/docs/OperationalIntent.md)
5. [docs/Theory.md](/home/goutev/LEAN4/info-geometry-lean/docs/Theory.md)
6. [lean/InfoGeometry/Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)
7. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
8. [tools/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/README.md)
9. [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md)

If you are operating as an agent inside this repo, also use:
- [skills/info-geometry-repo/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/SKILL.md)
- [skills/lean-canonicalization-policy/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md)

## Authoritative Surfaces

Trust current repo state in this order:
1. Lean source under `lean/InfoGeometry/`, especially `lean/InfoGeometry/Meta/`
2. the native audit entrypoint [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)
3. atomic DAG artifacts under [artifacts/dag](/home/goutev/LEAN4/info-geometry-lean/artifacts/dag)
4. derived readable reports under [reports/dag](/home/goutev/LEAN4/info-geometry-lean/reports/dag)
5. conceptual notes under [docs/](/home/goutev/LEAN4/info-geometry-lean/docs)

The most useful live reports are:
- [true-root-order.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/true-root-order.md)
- [representation-depth-audit.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/representation-depth-audit.md)
- [representation-depth-graph.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/representation-depth-graph.md)
- [theorem-surface-index.md](/home/goutev/LEAN4/info-geometry-lean/reports/dag/theorem-surface-index.md)

## Build

Use the locked wrapper for umbrella builds:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Audit
```

For the normal repo check surface:

```bash
lake script run strictCheck
```

## Maintained DAG Pipeline

The maintained pipeline is documented in [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md).
Run the Lean-native audit before treating the representation-depth Python views as authoritative.

After the main refresh sequence, the stable spine can be checked directly with:

```bash
python3 tools/infra/check_representation_depth.py
python3 tools/infra/generate_representation_depth_graph.py
```

## Documentation Policy

- `README.md`, `lean/DAG/README.md`, `tools/README.md`, and `tools/infra/README.md` are operational docs.
- [docs/OperationalIntent.md](/home/goutev/LEAN4/info-geometry-lean/docs/OperationalIntent.md) states why the repo, DAG, and infra tooling are maintained the way they are.
- [docs/Theory.md](/home/goutev/LEAN4/info-geometry-lean/docs/Theory.md) is the conceptual map of the stable spine.
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean) and [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean) are the native grammar and enforcement layer.
- `reports/` and `artifacts/dag/` are generated or regenerated surfaces.
- Python reports visualize and summarize the enforced structure; they do not define it.
- Stale prose loses to code and regenerated artifacts.
