# Attention polytope and token readout

## Ground-truth theorem contract

Base inspected: `ae969ffd788f9626ac789a9c128b0d920a6e98a0`.
Carrier: `Matrix (Fin n) (Fin m) ℝ`. Rows are queries; columns are keys.
Assumptions: entrywise nonnegativity and unit row sums. Matrices may be rectangular.
Owner reused: `DeterministicArgmaxAttention.deterministicAttention` from
`InfoGeometry.Canonical.DeterministicArgmaxAttention`; its entry is one exactly
when `j = f i`. Its existing row-sum theorem is reused without a replacement carrier.
The existing `InfoGeometry.Routing.FiniteSoftmax.weight` and normalization
lemmas are used in the softmax specialization. Square kernels connect to
Mathlib's `Matrix.rowStochastic`; convex combinations and vertex classification
use native `convexHull` and `Set.extremePoints`.

The target is the per-head post-softmax mixing operator and its action on
values, not the full nonlinear multihead/residual/normalization block.
The new mathematical result is explicit convex reconstruction, not Drazin
inversion, an eigenbasis, an orthogonal projection, or a physical interpretation.
The existing Birkhoff owner remains the separate, stronger column-balanced
case; ordinary attention is not silently Sinkhorn-normalized.

## Representation

For a complete route f, let D_f(i,j) = 1 when j=f(i), and zero otherwise.
The nonnegative rectangular row-normalized polytope is conv{D_f}, and its
extreme points are exactly the deterministic routing matrices D_f.
The explicit independent-coupling coefficients are λ_f = product_i A(i,f(i)).
They are nonnegative, sum to one, and satisfy A = sum_f λ_f D_f.

For values v_j in any real module, the i-th token readout is
sum_j A(i,j) v_j = sum_f λ_f v_(f(i)). Matrix form: AV = sum_f λ_f D_f V.
A one-hot query e_i extracts row i via e_i^T A. This is barycentric encoding
and readout, not projection of an arbitrary embedding onto a unique basis.
Routes are generally many-to-one. Their matrices compose by D_f D_g = D_(g∘f).
The rigidity theorem proves deterministic extremality, and the native
convex-hull theorem excludes any further extreme points.

With a mask, A(i,j)=0 at forbidden entries implies every positive-weight
route respects the mask. In particular, causal routes obey f(i) <= i.

For scores S and temperature τ, λ_f for row-softmax equals the existing
softmax applied to routeScore(f)=sum_i S(i,f(i)); the route partition function
is the product of row partition functions. The algebraic identity follows
Lean's total division convention at τ=0; ordinary temperature semantics use
τ>0. No token-independence assumption is made: independence specifies the
chosen coupling of row marginals, not a property of training data.

## Executable sparse representation

`tools/attention_polytope.py` uses exact Fraction arithmetic and returns a
sparse list of (weight, route) terms without enumerating m^n full routes.
At each step choose one positive residual entry per row, subtract the smallest
selected mass, and repeat. Residual row masses remain equal. Each nonfinal
step removes at least one positive entry, and the final step removes at least
one per row. Thus the number of terms is at most nnz(A)-n+1 <= n(m-1)+1.
This support-count argument is not mechanized as a Lean termination proof.
Every returned result is checked for exact mass, support, and reconstruction.

The sparse coefficients need not equal the product coefficients and are not
unique. Both give exactly the same matrix and token readout. There is no
claim of GPU speedup, differentiability of the greedy choices, or preservation
of gradients through a replacement backward pass.

Example (zero-based routes):

A = [[1/2,1/2,0], [0,1/3,2/3], [1/4,0,3/4]]
  = (1/4) D_(0,1,0) + (1/12) D_(0,1,2)
    + (1/6) D_(0,2,2) + (1/2) D_(1,2,2).

Run:

```bash
python3 tools/attention_polytope.py input.json
python3 -m unittest discover -s tests -p test_attention_polytope.py -v
```

The input JSON has `attention` and optional `values` matrices. Fractions may
be strings; decimal literals are parsed exactly. Normalization is rejected
unless separately requested with `--normalize-rows`, which reports whether
the matrix changed. The exact runtime requires nonempty rectangular inputs.

## Causal core diagnostic without route enumeration

For square causal attention, every deterministic route has only fixed-point
cycles. `Routing.CausalRouteDynamics` proves stabilization and constructs a
Drazin inverse from the stabilized power. `Routing.CausalCoreTrace` then proves
that **every exact causal routing mixture** has expected core trace `trace(P)`.
The product coupling and the runtime sparse coupling therefore agree on this
statistic, even though their individual routes can differ.

```bash
python3 tools/attention_polytope.py input.json --causal-core-only
```

This returns `expected_causal_core_rank`, its normalized fraction `trace(P)/n`,
and `route_decomposition_performed: false` for `n ≥ 1`. It validates nonnegative unit row
sums, square shape, and the lower-triangular mask. Dense input validation costs
O(n²) entry checks; the diagonal reduction costs O(n) additions, excluding
variable rational bit costs. No powers, SVD, MP shells, or routes are computed.

This is expected rank of the **route** core, not Drazin rank of the mixed matrix,
token-depth assignment, or semantic reasoning depth. Oblique shell operators
are not diagonal token labels. See [the scope contract](ATTENTION_ROUTING_DRAZIN_CONTRACT.md)
for the general deterministic Drazin/Birkhoff equivalence and remaining limits.
The Python implementation is tested separately, not extracted from Lean.
The Lean theorem certifies core-projector trace; the rank interpretation uses
the mathematical rank–trace identification, not a separate formalized rank
theorem in this bridge.

## Original polytope verification evidence

Lean source commit: `e612115829e5c2faffa47fd42a5fc5577c50285b`.
Successful scoped workflow: https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/39825545753
Job: `119987744001`, completed on 2026-10-22.

Both new modules compiled with Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. There are 25 new lemmas/theorems
(21 in AttentionPolytope and 4 in AttentionPolytopeSoftmax).
The six existing repository dependency modules were compiled from their
unchanged full source files before the two new modules.

The eight audited results (reconstruction, convex hull, vertex rigidity,
token and matrix readout, causal support, route-softmax equality, and softmax
readout) each report only `[propext, Classical.choice, Quot.sound]`.
The new Lean sources contain no `sorry`, `admit`, custom axiom or `native_decide`.

All 11 Python regression tests passed both locally and in this CI run.
They include exhaustive checks of 225 2-by-3 quarter-grid matrices and
1000 3-by-3 third-grid matrices, plus masks, readout, malformed input,
nonuniqueness, and the concrete example. Runtime tests are not a proof of
the Python implementation inside Lean.

Warnings: the core module has one unused `Function.comp_def` simp argument;
existing dependencies report deprecation/unused-section warnings. Checkout
cleanup also reports the pre-existing missing submodule URL for
`sandbox/Grassmann.jl`. None caused failure of the scoped check.

The workflow uses an isolated temporary checkout of the pinned Mathlib,
without changing root dependency pins or deleting caches. It compiles exact
repository owner files, prints axiom footprints, and rejects sorryAx.
This validates the two modules and their transitive owner closure; it is not
a full-repository build or a compiled test of the entire Routing.All umbrella.

Canonical local check in the full checkout:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Routing.AttentionPolytope \
  InfoGeometry.Routing.AttentionPolytopeSoftmax
```
