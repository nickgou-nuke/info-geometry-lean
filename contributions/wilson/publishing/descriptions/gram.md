## Why

Reflection-positive limiting Wilson correlations suggest a complex Gram
kernel on admissible test ensembles. Turning its finite definitions into a
Hilbert space requires actual nullspace quotients, compatible embeddings,
an algebraic direct limit, and completion. Analytic cutoff convergence and
the exact finite-family directed system are distinct steps.

## Changes

For an arbitrary Hermitian positive semidefinite complex kernel
`K : Matrix X X ℂ`, construct the Gram form on finitely supported complex
coefficients and its native separated Hilbert completion. The feature
vectors satisfy the exact complex identity `⟪feature x, feature y⟫ = K x y`.

For every finite family `F`, identify the finite Gram radical with
`ker (finiteEval K F)` and use Mathlib's `quotKerEquivRange` to realize the
actual quotient `(F → ℂ) ⧸ ker (finiteEval K F)` with its Gram geometry.
Coefficient zero extension preserves the entire sesquilinear form and
induces injective quotient maps.

The compatible finite stages form a native `Module.DirectLimit`. The
contribution proves its algebraic universal property, injectivity of its
canonical map, equality of its range with the finite-stage union, and
density. Its completion is canonically complex linearly isometric to the
kernel Hilbert space, with exact stage readback:

\[
\widehat{\varinjlim_F (\mathbb C^F/\operatorname{rad}G_F)}
\cong_{\mathbb C,\mathrm{isom}} H_K.
\]

A separate theorem passes eventual positive semidefiniteness through
entrywise kernel convergence along any nontrivial filter, using Mathlib's
closed positive cone. It applies to infinite label sets.

The construction adapts InfoGeometry's finite-stage completion pattern and
Mathlib's pre-inner-product construction. Apache provenance is retained.

## Validation

**Current verification:** exact destination Lean 4.36.0 passed in [run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500), job `139058006871`, at preparation source `ff8e1632b45569d88da1c73c0ec160c913fe55f9` against upstream `c25e77e9654a54fc5e4a04bfb637b7144defacc0`. The warnings-as-errors build, 29 fresh axiom reports, source-hash comparison and unchanged dependency-pin checks all passed. The current Lean files match that successful source inventory.

The patch includes a focused workflow and an audit of all public theorems
and the main completion/isometry constructions. From `LEAN/CoreLean`:

```sh
lake exe cache get
lake --wfail build CoreLean.PositiveKernelFiniteColimitAudit
lake env lean CoreLean/PositiveKernelFiniteColimitAudit.lean
```

The workflow requires the exact fresh axiom inventory with only the usual
`propext`, `Classical.choice`, and `Quot.sound` foundations, preserves the
existing dependency configuration, and archives its evidence. Coverage is
this contribution and its transitive imports; compiler results and checked
source hashes are recorded separately in the validation evidence.

## Scope

The project must provide the admissible Wilson labels, normalization and
reflection operations, kernel formula, cutoff convergence, and positivity.
The directed stages here use **one fixed limiting kernel**, so their
compatibility is exact. An arbitrary unbounded compatible family of linear
maps has an algebraic lift; no continuous extension is asserted without the
needed bounds. No full continuum gauge theory or mass-gap theorem follows
from this construction alone.
