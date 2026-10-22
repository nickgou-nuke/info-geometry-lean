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
Mathlib's `Matrix.rowStochastic`; convex combinations use `convexHull`.

The new mathematical target is explicit convex reconstruction, not Drazin
inversion, an eigenbasis, an orthogonal projection, or a claim about physical
space-time. The existing Birkhoff owner remains the separate, stronger
column-balanced case; ordinary attention is not silently Sinkhorn-normalized.

## Representation

For a complete route f, let D_f(i,j) = 1 when j=f(i), and zero otherwise.
The nonnegative rectangular row-normalized polytope is conv{D_f}.
The explicit independent-coupling coefficients are λ_f = product_i A(i,f(i)).
They are nonnegative, sum to one, and satisfy A = sum_f λ_f D_f.

For values v_j in any real module, the i-th token readout is
sum_j A(i,j) v_j = sum_f λ_f v_(f(i)). Matrix form: AV = sum_f λ_f D_f V.
A one-hot query e_i extracts row i via e_i^T A. This is barycentric encoding
and readout, not projection of an arbitrary embedding onto a unique basis.
Routes are generally many-to-one. Their matrices compose by D_f D_g = D_(g∘f).
The Lean rigidity theorem shows that no deterministic route is a nontrivial
positive mixture of other row-normalized nonnegative matrices.

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
This support-count argument is not yet mechanized as a Lean termination proof.
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

## Verification boundary

The local Python run passed 11 tests, including exhaustive checks of 225
2-by-3 quarter-grid matrices and 1000 3-by-3 third-grid matrices, plus masks,
readout, malformed input, nonuniqueness, and the concrete example.
These are runtime tests, not Lean proof authority.

Lean compilation was not available in the authoring session. The scoped
`attention-polytope.yml` workflow compiles the unchanged transitive repository
owner sources plus the two new modules against the exact Mathlib revision
and Lean toolchain recorded in the repository, in an isolated temporary clone.
It does not change root dependency pins or delete caches. It prints axiom
footprints and rejects sorryAx. The workflow result, not this document, decides
whether the Lean candidates compile. This is not a full-repository build.

Canonical local check in the full checkout:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Routing.AttentionPolytope \
  InfoGeometry.Routing.AttentionPolytopeSoftmax
```
