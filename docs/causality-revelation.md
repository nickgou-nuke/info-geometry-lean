# The Causal Proof Cone — A Revelation

## The System Built a Theory of Itself

On 2026-06-04, while auditing the InfoGeometry Lean 4 project, we discovered
that the system had formalized a theory of its own causal structure.

The dependency graph of Lean declarations — edges `A → B` meaning
"A is used in the proof of B" — is a **causal manifold** where each node is
an event (a declaration) and each edge is a causal relation.

## The Dictionary

The 2×2 tri-facet operator algebra, formalized in Bucket 3, is the **algebra
of causality** for this manifold:

| Operator | Matrix | Causal Role |
|---|---|---|
| **O** (tri-facet) | σ₁ = [[0,1],[1,0]] | Time-reversal: swaps past and future lightcones |
| **d** = (I+O)/2 | [[½,½],[½,½]] | Forward lightcone projector (consequences) |
| **δ** = (I-O)/2 | [[½,-½],[-½,½]] | Backward lightcone projector (dependencies) |
| **D** = d+δ | I | Dirac operator = every node is its own "now" |
| **Δ_H** = dδ+δd | 0 | Hodge Laplacian = acyclicity (no causal loops) |
| **Δ_D** = D² | I | Dirac Laplacian = invertible causal evolution |

## The Key Identities and Their Meaning

| Identity | Causal Interpretation |
|---|---|
| d² = d | Transitivity: the future of the future is the future |
| δ² = δ | Transitivity: the past of the past is the past |
| dδ = δd = 0 | **Acyclicity**: no closed causal loops (the DAG condition) |
| d+δ = I | Completeness: every edge is either forward or backward |
| d-δ = O | Chiral asymmetry: past ≠ future |
| Δ_H = 0 | **Harmonic causal structure**: the Hodge Laplacian vanishes |
| Δ_D = I | **Invertible causal evolution**: Dirac = identity |

## The Pipeline That Implements It

The Python toolchain in `tools/infra/` and `tools/leantrail/` operates on the
live ArangoDB topology overlay of the Lean dependency DAG:

### `tools/infra/arango_causal_chiral_cone_prompt.py`

Emit a causal/chiral cone prompt packet for one Lean declaration.
Navigates the backward cone (dependencies — δ edges) and forward cone
(consequences — d edges), applying Hodge/chiral/Dirac overlays.

### `tools/infra/arango_dag_algorithms.py`

The function `bounded_hodge_dirac_chiral_docs` computes:
- Laplacian eigenvalues (spectrum of causal connectivity)
- Chiral vertex grading (depth-parity assignments)
- Chiral edge grading (orientation of each dependency edge)
- Anticommutation violations (deviations from dδ = δd = 0)

### `tools/infra/graph_hodge_spectrum.py`

Computes global combinatorial Hodge invariants on the symmetrised graph
L = D − A:
- b₀ (connected components)
- b₁ bounds (Euler-Poincaré on the 2-complex)
- Fiedler λ₂ (algebraic connectivity)
- Kirchhoff index (effective resistance)
- Chiral grading (depth-parity mixing)

### `tools/infra/vacuity_critic.py` + `tools/leantrail/`

Discovers proof holes by walking the causal DAG. Each walk is a sequence
of d-steps (forward along consequences) and δ-steps (backward along
dependencies). The harmonic condition Δ_H = 0 guarantees path-independence.

## The De Bruijn-to-DAG Pipeline

```
Lean source .lean
  → compiler .olean (de Bruijn index encoding)
  → arango_raw_infotree_ingest.py (InfoTree extraction)
  → arango_dag_algorithms.py (DAG construction + SCC condensation)
  → topology_overlay edges (member_of_scc, scc_quotient)
  → Hodge/chiral/Dirac overlay (bounded_hodge_dirac_chiral_docs)
  → vacuity audit + LeanTrail proposals
```

## The K₀ Connection

The Grothendieck group of the proof DAG's monoidal category of declarations
— a Fibonacci ring ℤ[τ]/(τ² = τ + 1) — captures the quantum dimension
spectrum of causal connectivity. The golden ratio φ = (1+√5)/2 is the
spectral radius of the tri-facet matrix O.

The Verlinde S-matrix (S² = I, det(S) = -1, tr(S) = 0) diagonalises the
fusion algebra — it's the **discrete Fourier transform** of the causal
structure, relating forward and backward lightcones.

## Formal Statement

> **Causality = Acyclicity = Δ_H = 0 = dδ + δd = 0**

Every Lean development is a causally well-founded universe. The Hodge–Dirac
algebra — formalized in `InfoGeometry.Algebra.HodgeDiracDelta` and now
interpreted in `InfoGeometry.Causal.ProofCone` — is the grammar of its causal
structure. The Python pipeline computes it at scale. The Lean file is the
formal specification.

## What This Means

The system didn't just formalize abstract operator algebras or geometric
structures. It formalized the **causal fabric of formal proof itself** —
the very relation by which one theorem depends on another. The tri-facet
operator O is the time-reversal of the proof DAG. The Hodge Laplacian
vanishing is the acyclicity of implication. The Dirac operator being the
identity is the reflexivity of every node in causal time.

The Python pipeline, which builds the InfoTree from .olean files and computes
the causal/chiral cone for each declaration, is the **runtime** of this
causal algebra. The Lean file is its **axiomatic specification**.

And they converge because the same operator algebra governs both.
