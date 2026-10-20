# SAL/SAM and plabic-network archetypes

This note records a source-disciplined comparison between arXiv:2412.20018v2 and
the repository's plabic/Krein owners. It is an archetype map, not an asserted
isomorphism between neural networks and plabic graphs.

## Shared structural patterns

| SAL/SAM paper object | Repository-side archetype | Exact status |
| --- | --- | --- |
| Two interacting forward/backward streams | Bipartite/black-white or two-sheet carriers in `PlabicDiracKrein` and `FinitePlabicKasteleyn` | structural analogy only |
| A forward path and a feedback path | Boundary-measurement path sums and their dual edge directions | requires a typed path representation |
| Interstream error (E_v=V-\bar V^T) | An intertwiner defect (T-S^\ast) between two graph/operator actions | candidate theorem contract |
| Depth-chain telescoping | Composition of stage maps with an explicit residual | genuine categorical pattern, but no SAL instance yet |
| (H_D=M M^T\succeq0) | Gram positivity of a finite edge or boundary-measurement matrix | finite algebraic theorem candidate |
| Local outer-product plasticity | Edge-weight update on a fixed finite graph | requires a new update definition |
| Self-assembly from random connectivity | Dynamical graph evolution | interpretation; not present in current plabic owners |

## Causal order for a future formal bridge

\[
\text{finite directed two-stream graph}
\prec \text{path operators}
\prec \text{intertwiner defect}
\prec \text{defect cancellation}
\prec \text{path-composition residual}
\prec \text{Gram positivity}.
\]

The paper's empirical claims and its biological realizability axis are evidence and
interpretation nodes. They cannot be premises of Lean theorems. In particular, the
paper does not define a plabic graph, a positive Grassmannian chart, or a boundary
measurement map.

## Highest-return formal target

The smallest honest bridge is finite and algebraic:

1. choose a finite directed two-stream graph and two matrix-valued path operators;
2. define the defect (E=T-S^\ast);
3. prove the exact cancellation identity for matched outer-product updates;
4. prove (M M^T\succeq0) for the resulting aligned operator;
5. only then compare the path operator with an existing boundary-measurement map.

This ordering reuses the repository's existing plabic and Krein owners without
claiming that the paper's neural dynamics already instantiate them. A genuine
equivariant map, with its carrier and hypotheses, is required before any
`canonical_equiv` or physical interpretation edge is created.
