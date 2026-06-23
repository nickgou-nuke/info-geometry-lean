# Rohozhkin Delaunay Braiding Roadmap

**Source:** Illia E. Rohozhkin, *Pentagon equations, Delaunay
triangulations and pure braid group invariant*, Journal of Knot Theory and Its
Ramifications 34, article 2540007, 2025. DOI `10.1142/S0218216525400073`.

**Preprint lane:** arXiv `2405.10240`, with versions titled around
Voronoi/Delaunay triangulations and pure braid group invariants.

**Status:** source-ingestion and formalization specification; no new theorem
authority.

## Source Content

Rohozhkin constructs rational matrices attached to Delaunay flips of moving
points in the plane. With three fixed boundary points added, a motion of `n`
interior points is encoded by Delaunay triangulations with a fixed number of
triangles. At critical moments four points become cocircular and a Delaunay
diagonal flips. The flip is assigned a linear map between free rational modules
spanned by the triangle sets before and after the flip.

The main construction yields `(2n+1) x (2n+1)` matrices and a homomorphism from
the pure braid group on `(n+3)` strands to `GL_{2n+1}(Q)`.

## Source Anchors

- **Definition 2.1-2.4:** braid and pure braid group background.
- **Definition 2.5:** Voronoi diagram and Delaunay triangulation.
- **Lemma 2.1:** triangle count for the bounded Delaunay construction.
- **Definition 2.7:** flip group presentation and pentagon relation.
- **Section 4:** construction of the `(2n+1) x (2n+1)` flip matrices.
- **Equations 4.1-4.4:** source formulas defining the linear map/matrix for a
  flip.
- **Section 5 / Theorem 5.1:** product of flip matrices gives a well-defined
  pure braid group homomorphism.

## Existing Repo Anchors

- `InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding`
- `InfoGeometry.Canonical.YangBaxterProof`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge`
- `InfoGeometry.Projective.OctonionicKuzminBoundaryBridge`
- `InfoGeometry.Projective.SplitOctonions.OctonionicProjectiveLine`
- `docs/KASPAROV_KREIN_DIII_FIBONACCI_FOLLOWUP.md`

These are adjacency points only.  None of them currently proves Rohozhkin's
Delaunay flip matrix construction.

## Lean File Proposal

Suggested owner:

```text
lean/InfoGeometry/Projective/RohozhkinDelaunayBraiding.lean
```

### Phase 1: Finite Combinatorial Carrier

Define a finite, geometry-free carrier for source formulas:

```lean
structure DelaunayTriangleIndex where
  a : Nat
  b : Nat
  c : Nat
  hsorted : a < b /\ b < c

structure RohozhkinTriangulation where
  pointCount : Nat
  triangleCount : Nat
  triangles : Fin triangleCount -> DelaunayTriangleIndex

structure DelaunayFlip where
  before : RohozhkinTriangulation
  after : RohozhkinTriangulation
  quad : Fin 4 -> Nat
```

Initial closed targets should be readbacks, not geometry:

```text
triangle_count_planar_bounded_readback:
  under explicit source premises, triangleCount = 2*n + 1.

flip_preserves_triangle_count:
  before.triangleCount = after.triangleCount.
```

### Phase 2: Matrix Formula Owner

Define a rational matrix attached to a flip only after transcribing equations
4.1-4.4 exactly.

```lean
def rohozhkinFlipMatrix
    (F : DelaunayFlip)
    (hcount : F.before.triangleCount = 2*n + 1) :
    Matrix (Fin (2*n + 1)) (Fin (2*n + 1)) Rat := ...
```

Closed theorem targets:

```text
flip_matrix_size:
  the matrix has dimension (2*n+1) x (2*n+1).

flip_matrix_fixed_triangle_readback:
  basis vectors for triangles unaffected by the flip are mapped as specified
  by the source formula.
```

Do not assert invertibility until the exact inverse or determinant argument is
formalized.

### Phase 3: Pentagon Calculation

Encode only the finite five-flip pentagon word first:

```lean
structure PentagonFlipWord where
  T0 T1 T2 T3 T4 T5 : RohozhkinTriangulation
  f01 : DelaunayFlip
  f12 : DelaunayFlip
  f23 : DelaunayFlip
  f34 : DelaunayFlip
  f45 : DelaunayFlip
```

Closed theorem target after the exact matrices are in Lean:

```text
rohozhkin_pentagon_matrix_identity:
  product of the five source matrices is the identity matrix.
```

This should be proved by direct matrix computation for the minimal pentagon
block first, then lifted to larger matrices by an explicit block-extension
lemma.

### Phase 4: Pure Braid Homomorphism Interface

Only after the flip matrix formula and pentagon/far-commutativity relations are
closed:

```lean
structure RohozhkinBraidWord where
  initial : RohozhkinTriangulation
  flips : List DelaunayFlip
  returns_to_initial : Prop

def rohozhkinMatrixProduct (W : RohozhkinBraidWord) :
    Matrix (Fin (2*n+1)) (Fin (2*n+1)) Rat := ...
```

Conditional theorem target:

```text
rohozhkin_pure_braid_homomorphism:
  assuming the source isotopy move classification and verified matrix
  relations, the matrix product is invariant under pure braid isotopy.
```

The isotopy classification should remain an explicit theorem parameter unless
the repo formalizes the topology of braid isotopies.

## Bridge to Existing Fibonacci/MZM Lane

The safe first bridge is not a physics theorem.  It is a typed interface saying
that a Rohozhkin matrix product can serve as a finite braid readout under
explicit assumptions.

```lean
structure RohozhkinFibonacciBridgePremises where
  rohozhkinMatrix : Matrix (Fin m) (Fin m) Rat
  fibonacciGate : ExistingFibonacciGate
  phaseReadout : Rat -> ExistingPhaseType
  compatibility : Prop
```

Allowed theorem shape:

```text
rohozhkin_fibonacci_readout:
  if an explicit compatibility premise identifies a Rohozhkin matrix product
  with an existing Fibonacci braid gate, then the existing Fibonacci rewrite
  lemmas apply.
```

Forbidden theorem shape:

```text
Rohozhkin matrices prove Majorana scrambling / horizon unitarity / black-hole
information preservation.
```

Those claims require separate geometric and analytic premises not supplied by
Rohozhkin's paper.

## Open Debt

1. **Exact matrix transcription.**
   Equations 4.1-4.4 must be transcribed into Lean over `Rat`.

2. **Delaunay geometry.**
   The repo does not own Euclidean Voronoi/Delaunay geometry, cocircular event
   classification, or general-position topology.

3. **Move classification.**
   The proof of homomorphism uses codimension-one and codimension-two events in
   isotopies of point motions.  This should remain an explicit source theorem
   parameter until formalized.

4. **Matrix relations.**
   Far commutativity and pentagon matrix identity need direct finite proofs.

5. **Braid representation.**
   The pure braid group presentation and the target `GL_{2n+1}(Q)` need a
   formal owner if the repo wants an internal theorem rather than a source
   readback.

6. **Fibonacci/MZM interpretation.**
   Any connection to Fibonacci anyons, Majorana zero modes, or horizon
   scrambling must be an interface theorem over explicit compatibility data.

## Verification Plan

For the first Lean owner:

```bash
lake env lean lean/InfoGeometry/Projective/RohozhkinDelaunayBraiding.lean
lake build InfoGeometry.Projective.RohozhkinDelaunayBraiding
rg -n "sorry|admit|axiom|: True := by|theorem .*: True|_valid|_certificate|law_holds" \
  lean/InfoGeometry/Projective/RohozhkinDelaunayBraiding.lean
```
