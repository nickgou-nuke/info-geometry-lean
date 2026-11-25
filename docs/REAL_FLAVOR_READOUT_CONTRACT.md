# Real flavor readout, Dirac transport, and compression

## Intake and provenance

The requested addition follows the source audit of
[`theaiwillwin/octonionic-flavor-research` at `fcdb44161381be4537a7f3fb749cf410b6c1dd4c`](https://github.com/theaiwillwin/octonionic-flavor-research/tree/fcdb44161381be4537a7f3fb749cf410b6c1dd4c).
The principal research inputs are the corrected covariance discussion in
`PARSED_RESEARCH_SYNTHESIS.md`, the signed channel in
`bifundamental_covariance_gate_v1.py`, and the quadratic compression certificate
in `TARGET_FREE_BIFUNDAMENTAL_NO_GO_THEOREM_v1.md`. They motivate targets;
their numerical receipts do not certify the Lean declarations.

Implementation base: `fe24e350b08fdea04f74c0748ef9fd9417c47529` of
`nickgou-nuke/info-geometry-lean`. Lean and dependency pins are unchanged:
Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Exact mathematical contract

All coefficient fields in the new mathematical owners are real. Index types
are finite; decidable equality is required where identity matrices are used.
Matrix multiplication retains its order throughout.

### 1. Signed rectangular readout

For `T : Matrix m n ℝ`, `L : Matrix n p ℝ`, and
`R : Matrix m q ℝ`, define

\[
Y(T,L,R)=(TL)^T R.
\]

The left column is acted on by `T` before pairing with a right column. Thus
`Y = Lᵀ Tᵀ R`, with this transpose convention fixed throughout. Arbitrary
rectangular column changes obey

\[
Y(T,LU,RV)=U^T Y(T,L,R)V.
\]

An actual operator intertwiner `T' V = U T` and an output isometry `UᵀU=1`
give ambient-transport invariance. Native orthogonal-group instances provide
the usual simultaneous transport of operator and frames. Left and right
Gram covariance follows with the required orthogonality assumptions.

The obstruction theorem quantifies over an arbitrary matrix-valued function:
evenness in the left frame together with signed orthogonal covariance forces
that function to vanish. The explicit counterexample squares scalar readout
entries of a nonzero off-diagonal 2×2 matrix. It is not identified with the
external archive's vector-valued associator-norm table.

### 2. Existing Dirac operator and its Gram blocks

`InfoGeometry.Streaming.BipartiteGraphDirac` already owns the real linear
operator `graphDirac B` on a product of finite coordinate spaces. Instantiate
it with `B = Yᵀ`:

\[
D_Y(x,y)=(Yy,Y^Tx),\qquad \Gamma(x,y)=(x,-y).
\]

The native `LinearEquiv.sumArrowLequivProdArrow` intertwines this owner with
the block matrix `[[0,Y],[Yᵀ,0]]`. The bridge reuses the owner's oddness,
positive-pairing self-adjointness, and square. Native block multiplication
gives `D_Y² = diag(YYᵀ,YᵀY)` in matrix coordinates. Frame covariance transports
this block matrix by the two block-diagonal frame matrices.

Both Gram blocks are native `Matrix.PosSemidef`. For a rectangular `m × n`
matrix, retain the exact dimension correction:

\[
X^{|n|}\chi_{YY^T}=X^{|m|}\chi_{Y^TY}.
\]

This gives the same nonzero real characteristic roots. It does not assert
equal zero multiplicities when the two dimensions differ.

### 3. Orthogonal compression and conditional saturation

For `RᵀR=1`, write `P_R=RRᵀ`. The generic orthogonal-compression target is

\[
\|W\|_F^2=\|W^TR\|_F^2+\|(1-P_R)W\|_F^2.
\]

The scaled-projector specialization supplies explicit hypotheses on a real
matrix `T`, an orthogonal projector `P`, and an orthonormal left frame `L`:
`TᵀT = c² • P`, `Pᵀ=P`, `P²=P`, and `LᵀL=1`. These hypotheses yield

\[
c^2 |p|-\|Y(T,L,R)\|_F^2
=c^2\|(1-P)L\|_F^2+\|(1-P_R)TL\|_F^2.
\]

The bound and its equality conditions are consequences of this identity and
positivity. At saturation the left Gram is `c² • 1`. The zero-scale case is
handled without inferring rank or nonzero singular values. With three left
columns, scale `c=2`, and two right frames, the summed bound is `24`.

The projector identity is a mathematical assumption of this generic theorem;
the addition does not assert that an octonion associator satisfies it.

## Owner reuse and causal order

| New owner | Existing declarations and missing implication supplied |
|---|---|
| `Canonical.FlavorReadout` | Native transpose/multiplication and orthogonal-group laws; existing `Canonical.MatrixTwoNoncommutativity` matrix unit. Supplies the explicit bilinear readout and its covariance/obstruction. |
| `Canonical.FlavorDiracGram` | `Streaming.BipartiteGraphDirac`, native sum/product linear equivalence, `Matrix.PosSemidef`, and `Matrix.charpoly_mul_comm'`. Supplies the matrix/operator transport and readout-to-Dirac covariance. |
| `Canonical.FlavorCompression` | Native Frobenius norm, trace, transpose, and matrix multiplication. Supplies the orthogonal-compression loss identity and conditional equality consequences. |

The dependency order is signed readout → frame transport → represented Dirac
operator/Gram blocks; independently, orthogonal projection → compression loss
→ scaled-projector bound → saturation. A conceptual resemblance is not used as
a dependency edge.

Bounded owner search covered readout/bifundamental/frame-covariance variants,
the graph Dirac/Hodge owners, Hilbert–Schmidt trace owners, and existing Peirce
compression lemmas. The new rectangular compression theorem has different
carriers and hypotheses from the existing double-sided Peirce constructions.

## Explicit remaining obligations

- Specialize the generic operator to ordinary division octonions and prove
  the universal associator/projector identity, including degenerate pairs.
- Keep the compact positive-norm algebra distinct from split octonions and
  `G₂(₂)`. No change of real form is inferred from these matrix results.
- Prove a separate local-minimum classification if one is desired. A
  semidefinite Hessian does not establish a local minimum; quartic descending
  directions remain possible.
- A single channel's representational capacity and the spectra selected by a
  specified action are different questions. No universal necessity of a
  second channel is asserted.
- No physical Yukawa identification, observed masses, CKM/PMNS prediction,
  Standard Model derivation, independent Krein mirror, or smooth groupoid is
  claimed by these finite real statements.

## Validation record

On 2026-11-24, the focused final invocation completed successfully on the
mathematical sources below using Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The run built all three owners, freshly elaborated each with
`-DwarningAsError=true`, and completed the native owned-declaration audit.
It accepted **54 declarations**: 19 in `FlavorReadout`, 14 in
`FlavorDiracGram`, and 21 in `FlavorCompression`. This includes generated
and private declarations; only `propext`, `Classical.choice`, and `Quot.sound`
were permitted as foundational axiom dependencies. Source, configuration,
dependency, and runtime stability checks passed.

The receipt is `verification.json` in run
`run-1795535006720152153-5` under `artifacts/verification/real-flavor`.
The verified source SHA256 values are:

| Owner | SHA256 |
| --- | --- |
| `FlavorReadout` | `291083a41306a061fd19dbe9ea1398af19157f63d03d40dc5e551fde2dc38348` |
| `FlavorDiracGram` | `5cb8c596855d302a0507572a70afb48c7337c7ec1248f49a4598e70ac1e8f891` |
| `FlavorCompression` | `02135f1b13df9acd0e0940e73089104a1fc9c267eeccb5c160b28b164717f2ee` |

The strict staged proof gate, installed pre-commit hook, whitespace check,
and independent source reviews also passed. The addition retains 49 theorem
declarations and two definitions. Compiler-driven repairs supplied native
orthogonal-group parameters and the real star-order instance, completed the
grading and zero-scale simplifications, and removed unused implicit
instances without disabling linters.

The maintained publication gate is separate. Its root Lake build failed
because the configured package `external_refs/homotopy-hypothesis-lean4`
is unavailable. Its scoped source-only audits passed. Focused acceptance
does not certify that root package or assert successful hosted CI. Existing
mathematical owners, toolchain pins, and repository gate implementations
remain unchanged.
