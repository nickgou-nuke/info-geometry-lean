# Operational Intent

This repository is one theory with several representation levels.
The main formal burden is to make the morphisms between those levels explicit, adjacent, and checkable.

## What Is Being Formalized

The stable spine is a representation ladder:
- `L0` count / relative-volume data
- `L1` projective / gauge / relative-potential data
- `L2` operator / partition / modular-lift data
- `L3` Krein / Clifford / polarized-sheet data
- `L4` transport / Bogoliubov / spectral-change data
- `L5` thermodynamic / attention / Gibbs-Sinkhorn data

The important mathematical content is not only the objects at each layer.
It is the enforced morphisms between them:
- owner definitions at the lowest natural level
- adjacent translators between neighboring levels
- coherence theorems proving that rival adjacent composites agree
- capstones that summarize lower content without pretending to be foundational owners

## What Canonical Means

`canonical` means the stable public owner surface.
It does not mean the only valid mathematics in the repository.

Valid but unfinished mathematics should be:
- developed on noncanonical or exploratory surfaces
- quarantined honestly when it is not yet stable
- promoted when the owner-level proofs become real

What should be removed are theorem-shaped wrappers and facade surfaces that do not carry mathematical load.

## Why DAG And Python Tooling Exist

The DAG and infra layers were developed to preserve operational memory and make the repository readable after context loss.
They serve four jobs:

1. externalize dependency memory from the Lean environment into stable artifacts
2. expose owner / translator / coherence / capstone pressure on the declaration graph
3. surface theorem-wrapper burden, representation-depth legality, and residual comparison debt
4. give CI and humans a reproducible view of the current structural state

They do **not**:
- define mathematical truth
- replace direct code reading
- invent ontology that is absent from Lean
- justify deleting valid mathematics by heuristic alone

## Tooling Contract

The trusted order is:
1. Lean source
2. Lean-native audit
3. atomic DAG artifacts
4. derived Python reports
5. prose

The DAG layer is maintained because raw code reading alone does not scale once the theory spreads across many representation surfaces.
The Python layer is maintained because regenerated reports are the fastest way to recover context, localize debt, and choose the next honest file to inspect.

## Process-Flow Layer

The newer process-flow tooling is specifically for constitutive transport evidence.

Lean side:
- [ProcessFlowExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ProcessFlowExport.lean)

Python side:
- [generate_process_flow_report.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_process_flow_report.py)

This layer exists to make local flow evidence explicit:
- `FlowEdge` as the primitive carrier
- `ProcessEvent` as edge aggregation
- bounded path candidates as secondary derived objects
- localized defect rows
- derived comparison and cocycle reports downstream

Its purpose is to audit transport and coherence pressure, not to replace theorem proofs.

## Default Reading Order

When context has been purged, rebuild intention in this order:
1. [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
2. [lean/InfoGeometry/Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)
3. [docs/Theory.md](/home/goutev/LEAN4/info-geometry-lean/docs/Theory.md)
4. [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
5. [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md)
6. the specific owner files and regenerated reports relevant to the task
