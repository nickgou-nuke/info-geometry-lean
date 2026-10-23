# Functional routes: SVD-free fiber runtime

The standard-library module `tools/functional_route_fibers.py` uses Fraction
arithmetic. The optional PyTorch snapshot logger is
`tools/route_diagnostics_torch.py`. Neither modifies a training loop or
replaces Autograd. This implementation distinguishes deductions below from
claims in the uploaded proposal; runtime tests are not Lean kernel proofs.

For A(i,j)=1[j=f(i)], recurrent restriction sigma, and first-entry depth d(i),
let rho(i)=sigma^(-d(i))(f^d(i)(i)). Define E(i,j)=1[j=rho(i)], F=I-E,
N=A F. The graph solver computes E and D as sparse maps in O(n) graph work.
Its `entry_depth_counts` and `shell_ranks` are deliberately different fields.

For m>=1, the row of N^m at i is zero when d(i)<=m; otherwise it is
`e_(f^m(i))-e_(rho(f^m(i)))`. For each active transient target j let
F_m(j)={i:d(i)>m and f^m(i)=j}. Let U_m be fiber membership and let B_m
have rows e_j-e_rho(j). Then N^m=U_m B_m. U_m has disjoint nonempty columns;
B_m has full row rank because its transient-column submatrix is identity.
Therefore the actual ambient range projector is

    P_m=U_m (U_m^T U_m)^(-1) U_m^T,

which averages within fibers. This is an equality for N^m, not a substitution
of an unrelated zeroed-tree operator. At m=0 use P_0=I.

The actual MP inverse is

    (N^m)^dagger=B_m^T (B_m B_m^T)^(-1)(U_m^T U_m)^(-1)U_m^T.

For targets sharing an anchor rho(j), the corresponding B_m B_m^T block is
I_s+11^T and its inverse is I_s-11^T/(s+1). The implementation applies these
blocks by fiber averages and anchor-wise corrections, without SVD.
The new Lean `mp_of_split_factorization` derives the Penrose equations from
split-factorization and support-symmetry hypotheses. The construction of U_m
and B_m and verification of those hypotheses for every graph are not yet
mechanized. No pseudoinverse covariance under oblique similarity is assumed.

Dressed shell action is H_0 V=F V, H_m V=P_m F V for m>=1, and
S_m V=H_m V-H_(m+1) V. All shell applications use O(k*n*d) arithmetic and
O(n*d) generator working memory. Storing all outputs costs O(k*n*d).
Materializing dense shells costs at least O(k*n^2) output entries.
These are arithmetic-operation counts, not Fraction bit-complexity bounds.

For I_m=im f^m, rank(S_m)=|I_m|-|I_(m+1)|. Transient j is in I_m iff its
maximum incoming transient-path length h(j) is at least m. Hence
rank(S_m)=#{j transient:h(j)=m}. Kahn peeling computes the whole shell-rank
histogram in O(n), but it does not identify shells with depth-selected nodes.
For f=(0,0,1,1), entry counts=(1,2), shell ranks=(2,1).

## Correct truncated readout

The logger returns unnormalized retained-core and retained-nilpotent outputs,
plus residual_output. Their sum reconstructs P V up to floating-point rounding.
It does not discard residual mass or silently renormalize P. Conditional
route statistics use a `conditional_` prefix; zero retained mass gives NaN
for those conditional statistics. Causal expected core fraction is trace(P)/n,
using the existing CausalCoreTrace theorem rather than route enumeration.

A convex route decomposition is not a Drazin decomposition of P itself.
Most route statistics depend on the chosen coupling. Graph entry depth is
not an established measure of reasoning depth. Caratheodory pruning for fixed
V may change P and route statistics. Rectangular routing cannot be iterated
without extra structure. No interactive explorer or GPU speedup is claimed.

## Use and tests

```python
from tools.functional_route_fibers import analyze_route, shell_actions
g=analyze_route([0,0,1,1])
assert g.entry_depth_counts==(1,2)
assert g.shell_ranks==(2,1)
for m, result in enumerate(shell_actions(g, [[1],[2],[3],[4]])):
    print(m, result)

from tools.route_diagnostics_torch import FunctionalRouteDiagnostics
# attention: (...,n,n), values: (...,n,d), matching batch/dtype/device
# result=FunctionalRouteDiagnostics(4)(attention, values)
# output=result['reconstructed_output']
```

```bash
python3 -m unittest discover -s tests -p test_functional_route_fibers.py -v
python3 -m unittest discover -s tests -p test_route_diagnostics_torch.py -v
```

All 11 tests passed locally with torch 2.10.0+cpu. The exact subset checks all
288 maps on n=1,2,3,4, plus mixed-cycle examples up to n=8, against Drazin
identities, minimal witness index, all four Penrose equations for powers,
shell products, telescoping, recovery, and rank. Torch tests cover batching,
causality, truncation/residual, validation, and no input mutation or gradients.
The dedicated Lean workflow does not run the optional torch suite. No
end-to-end training integration or formal proof of the Python code is claimed.
