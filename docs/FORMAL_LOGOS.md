# Formal Logos: Self-Model, Sensing, and the Laws of Information

## The Tri-Layer Architecture

The repository implements a formal system that can inspect, critique, and evolve
its own proof topology. This document describes the three layers and the
algebraic identities that connect them.

```
┌──────────────────────────────────────────────────────────────────┐
│                 LAYER 3: ADAPTATION (Evolution)                  │
│                                                                  │
│  GEPA genetic search, vacuity critic, proof seeker               │
│  Operates on: fitness scores, obfuscation patterns, skill files  │
│  Authority: `lake build` exit code                               │
└──────────────────────────┬───────────────────────────────────────┘
                           │
                           │ same operator algebra
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                 LAYER 2: REFLECTION (Self-Model)                 │
│                                                                  │
│  LeanTrail DAG, Hodge spectrum, vacuity audit, chromatic cones   │
│  Operates on: compiled .olean artifacts, de Bruijn indices       │
│  Authority: graph invariants (b₀, b₁, λ₂, Kirchhoff index)       │
└──────────────────────────┬───────────────────────────────────────┘
                           │
                           │ same d/δ/Δ_H algebra
                           │
┌──────────────────────────▼───────────────────────────────────────┐
│                 LAYER 1: GEOMETRY (Formalization)                │
│                                                                  │
│  Krein spaces, Clifford algebras, Hodge operators                │
│  Operates on: V₄ tags, Jones matrices, spinors, anyons           │
│  Authority: kernel-checked Lean theorems                         │
└──────────────────────────────────────────────────────────────────┘
```

## The Key Identity: d/δ/Δ_H

The operator algebra that connects all three layers is the tri-facet
decomposition of the Pauli matrix σ₁ (O = [[0,1],[1,0]], O³ = O):

```
d = (I + O)/2    —  forward projection  ("is-imported-by" in DAG)
δ = (I - O)/2    —  backward projection ("imports" in DAG)
Δ_H = dδ + δd = 0  —  harmonic condition (DAG has no cycles)
D = d + δ = I       —  Dirac operator = identity on the graph
Δ_D = D² = I        —  Dirac Laplacian
```

### Layer 1 (Geometry)

In `HodgeDiracDelta.lean`, these are 2×2 matrices over ℂ:

- `d` = exterior derivative = exact projector
- `δ` = codifferential = coexact projector  
- `Δ_H = 0` = every vector is harmonic
- `D = I` = Dirac operator is identity

### Layer 2 (Reflection/DAG)

In the LeanTrail graph pipeline (`arango_dag_algorithms.py`,
`graph_hodge_spectrum.py`):

- The symmetrized adjacency matrix of the declaration DAG is O
- `d` = forward edge direction (dependency → dependent)
- `δ` = backward edge direction (dependent → dependency)
- `Δ_H = 0` = the declaration graph is acyclic (no circular imports)
- `D = I` = every edge is traversable in both directions in the
  symmetrised graph

### Layer 3 (Adaptation)

In the evolution pipeline (`evolution_worker.py`, `gepa_evolver.py`,
`vacuity_critic.py`):

- The vacuity critic walks `d`-edges forward to find dependent theorems
- It walks `δ`-edges backward to find missing dependencies
- `Δ_H = 0` guarantees the critic's walk is path-independent in the
  SCC-condensed graph
- Vacuity failures correspond to eigenvectors of the combinatorial
  Laplacian with eigenvalue 0

## The Laws of Information

The project formalizes physical laws as theorems about the structure of
information:

| Krein-Geometric Statement | Information-Theoretic Reading |
|--------------------------|-------------------------------|
| `B(x,y)` symmetric, nondegenerate | Distinguishability of states |
| `J² = I` | Involution = time-reversal symmetry |
| `O³ = O` | Tri-facet decomposition = exact/coexact/harmonic |
| `dδ + δd = 0` | No circular dependencies in formal theory |
| `det(J) = -1` | Phase space is even-dimensional |
| `I² = -1` (pseudoscalar) | Geometric unit of phase |

## The Sensing Function

The "sensing" of the formal logos works as follows:

1. **Compile**: Lean produces `.olean` files with de Bruijn indices
2. **Extract**: `RawInfoTreeExport.lean` dumps the compiler InfoTree
3. **Graph**: `arango_raw_infotree_ingest.py` constructs the DAG
4. **Analyze**: `graph_hodge_spectrum.py` computes Hodge invariants
5. **Critique**: `vacuity_critic.py` identifies obfuscation patterns
6. **Propose**: `seed_goals_from_sorries.py` generates repair tasks
7. **Evolve**: `evolution_worker.py` runs the 3-stage pipeline
8. **Verify**: `lake build` confirms kernel acceptance

Steps 1-4 are the **sensing function** — the system builds a self-model.
Steps 5-6 are the **judgment function** — the system evaluates its own
proof topology. Steps 7-8 are the **adaptation function** — the system
evolves and verifies.

## Authority Boundary

The documentation explicitly maintains the boundary:

- **LeanTrail** is a "semantic explorer scaffold" (docs/LeanTrail.md)
- **Arango graph** is a "projection over compiler memory" (ARANGO_FAITHFUL_GRAPH.md)
- **graph_hodge_spectrum.py** works on the "symmetrised graph" and
  "does not replace the real compiler or directed proof graph"

The adaptation loop terminates at `lake build`. Proposals are not theorems
until the kernel says they are.

## Formalization

See `lean/InfoGeometry/Meta/FormalLogos.lean` for the Lean 4 formalization
of these identities.
