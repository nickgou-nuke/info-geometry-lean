# Chiral determinant lines and occupied-frame overlaps

## Provenance and acceptance boundary

This contract records the corrected finite mathematical content of the user
intake `Pasted text(20261117-142336).txt`, received on 2026-11-17. The original
33,197-byte attachment is preserved separately, with SHA-256
`0aaff08f49df71cc72b00563b0bba85d49726ccb7a06cfa31079e00a151567e2`.
The original prose is a source of proposed claims, not proof evidence.

Implementation starts at upstream `08c34e03f610b452e03422037949196dc7d92d6d`.
The unchanged environment is Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The accompanying review records
actual compilation, source-gate, and publication results separately. No theorem
in this contract should be labelled kernel verified before its native check
finishes successfully.

## Atomic claim ledger

| Claim | Correct contract and disposition |
| --- | --- |
| A chiral map has distinct source and target. | Keep `f : V →ₗ[K] W` with separately typed modules. Inequivalent spin representations need not be nonisomorphic as underlying vector spaces. |
| The determinant is intrinsically a scalar. | Construct the actual exterior map `Λⁿ f` and its canonical tensor in `(Λⁿ V)* ⊗ Λⁿ W`. This carrier has dimension one when both finite dimensions are `n`. A scalar coefficient requires two frames. |
| The determinant amplitude and fermion measure are the same line. | With `f : V → W`, the amplitude is in `(det V)* ⊗ det W`; a measure pairing with it is in the dual line `det V ⊗ (det W)*`. Fix this orientation before comparing constructions. |
| Independent frame changes alter the phase. | For `M = Lᴴ D R`, prove `M' = U₋ᴴ M U₊` and its determinant law. Calling this coordinate covariance a gauge anomaly requires additional family and descent data. |
| An overlap is a Slater exterior pairing. | Construct the column blade and the conjugate-column dual blade with native exterior powers, then prove their canonical dual pairing equals `det(Lᴴ R)`. No complex exterior Hilbert-space instance is assumed. |
| The modulus depends only on occupied projectors. | For `RᴴR=1`, prove `star(det(LᴴR))*det(LᴴR) = det(1-Pᵣ+PᵣPₗPᵣ)`, where `Pₗ=LLᴴ`, `Pᵣ=RRᴴ`. The additional assumption `LᴴL=1` makes `Pₗ` an orthogonal projector as well. |
| Compression always preserves the full chiral Gram operator. | Always retain `LLᴴ` in `MᴴM = RᴴDᴴLLᴴDR`. Removing it requires the explicit range-support equation `(LLᴴ)DR=DR`. |
| Positive-mode pairing proves equality of kernels. | Reuse existing AB/BA and Hilbert Gram owners; positive eigenspaces pair, while kernel and cokernel can differ. This PR does not duplicate PR373's normalized eigenspace isometry. |
| A zero mode forces a primed zeta determinant to vanish. | Rejected: a primed determinant omits zero modes. `diag(1,0)` has ordinary determinant zero but reduced positive-mode product one. Analytic regularization is outside these finite owners. |
| Nonzero index forces the source Gram determinant to vanish. | Rejected: the inclusion `ℂ → ℂ²`, `z ↦ (z,0)`, has index `-1` and `DᴴD=1`. Index measures kernel minus cokernel, not an inequality of ambient infinite Hilbert dimensions. |
| Exactly the absolute index counts all required zero-mode insertions. | Extra paired zero modes are possible. All kernel and adjoint-kernel Grassmann coordinates must be saturated; their signed difference is the index. |
| Flatness is equivalent to any scalar trivialization. | Rejected. A curved connection may live on a trivial line; a flat connection may have nontrivial holonomy. Trivial holonomy characterizes a unit parallel trivialization under the appropriate geometric hypotheses. |
| The determinant holonomy is `exp(-π i ξ)` with `ξ=(η+h)/2`. | For Freed's determinant convention and bounding circle spin structure, the formula is the adiabatic limit of `exp(-2π i ξ)`. A half exponent concerns an additional Pfaffian/square-root construction. |
| A causal poset proves a unique global physical synthesis. | No such implication is established. Only explicit maps, equalities, and theorem dependencies are used below. |

## Native owners and the smallest missing implications

The bounded search inspected canonical and legacy source, imported definitions,
instances, theorem bodies, and concrete consumers. It found:

- `Projective/ExteriorKleinDeterminantCovariance`: a genuine exterior-power
  coordinate law, specialized to real four-dimensional endomorphisms.
- `Volume/DeterminantBundle`: `DeterminantLine V := ℝ`, a scalar model with
  scaling, rather than the two-space exterior tensor required here.
- `Canonical/DeterminantPhaseVolumeBridge` and
  `Canonical/RelativeDeterminantScatteringSocket`: supplied readout interfaces,
  not determinant constructions.
- `LinearAlgebra/FiniteGramDeformationEntropy` and
  `Canonical/FiniteBogoliubovFrameDeformationEntropy`: square-frame determinant
  and polar-volume results; the latter assumes invertible complex frames.
- `OperatorAlgebra/PartnerEigenspaces` and `Analysis/HilbertGramDuality`:
  actual positive-eigenvalue pairing between different carriers. PR373 extends
  this to normalized Hilbert eigenspace isometries.
- `Clifford/Cl55ChiralSectorPredicateBridge`: native real chiral sectors of
  dimension sixteen and a proved bijective positive-generator exchange map.
- PR395's `RectangularProjectorStabilization`: ordered trace/curvature
  stabilization, without a determinant stabilization theorem.

The new finite owners use Mathlib's `exteriorPower.map`,
`dualTensorHomEquiv`, `exteriorPower.pairingDual_ιMulti_ιMulti`, native basis
transport, `Matrix.det_one_add_mul_comm`, and conjugate transpose. They do not
rebuild a determinant, assume an unknown determinant readout, or replace ordered
matrix products with scalar models. The new PR is based on `main`; it does not
require the unmerged PR373 or PR395.

## Theorem contracts

### Exterior determinant tensor

Over a field `K`, a finite-dimensional source gives the canonical tensor

\[
\operatorname{detTensor}_n(f)
 = \operatorname{dualTensorHomEquiv}^{-1}(\Lambda^n f)
 \in (\Lambda^nV)^*\otimes_K\Lambda^nW.
\]

Its readback is the actual exterior map. If both dimensions are `n`, its carrier
has dimension one, and its nonvanishing is equivalent to bijectivity of `f`.
For bases `b,c`, the coefficient is `c.det (f ∘ b)`. The ordered frame law is

\[
d_{b',c'}(f)=c'.\det(c)\,d_{b,c}(f)\,b.\det(b').
\]

The target factor is inverse frame transport. An inverse can be identified
with an adjoint only with suitable unitary/orthonormal hypotheses. The native
`Cl(5,5)` consumer uses the existing sixteen-dimensional chiral-sector map;
its distinguished positive generator has a nonzero determinant tensor. This
is finite Clifford action, not an elliptic or lattice Dirac theorem.

### Rectangular stabilization and overlap

For rectangular `U,V` over a commutative ring, `VU=1` implies

\[
\det\bigl(UAV+(1-UV)\bigr)=\det A.
\]

No invertibility or idempotence of `A` is needed. The proof uses the native
rectangular Sylvester identity. For a commutative star ring and equally many
columns in `L,R`, ordered compression and determinant covariance then yield
the Gram and projector-modulus formulas in the ledger. The matrix algebra
itself is noncommutative throughout.

The Slater consumer evaluates actual degree-`n` primal and dual exterior
blades. With a rectangular `D`, it applies `ΛⁿD` before pairing with the left
dual blade. This evaluation equals `det(LᴴDR)`. Singular overlaps are allowed.
For occupied rank zero the overlap is one, as required by the empty determinant.

## Established dependencies versus analytic obligations

The finite dependency order is: native linear map and exterior functor;
tensor--Hom identification and determinant coordinates; independent frame
covariance; rectangular determinant stabilization; Gram/projector modulus;
native Slater and chiral-sector consumers. These are algebraic implications,
not a proof of equivalence between continuum and lattice constructions.

Still required for such a comparison are operator domains and Fredholm
families, elliptic spectral theory, regularized determinants, full complex
spectral-band gluing, a smooth determinant bundle and Quillen metric,
Bismut--Freed connection, eta/adiabatic holonomy, gauge equivariance and
descent, and a controlled continuum limit. A positive Hilbert norm, a finite
determinant identity, or a hand-built dependency poset supplies none of these
analytic constructions by itself.

## Primary sources and external comparison

- [Freed, *On Determinant Line Bundles*](https://people.math.harvard.edu/~dafr/detsur.pdf),
  Theorem 1.12 and equations 1.13--1.21 for the line, section, and metric;
  Theorem 1.31 for determinant holonomy; Theorem 3.1/equation 3.3 for the
  additional square-root construction. Spectral-band gluing retains the full
  determinant isomorphism, including phase.
- [Dai--Freed, *Eta-Invariants and Determinant Lines*](https://arxiv.org/abs/hep-th/9405012),
  introduction, Proposition 2.15, and section 5: exponentiated reduced eta
  invariant, inverse-line convention, and spin-structure signs.
- [Freed, *Anomalies and Invertible Field Theories*](https://arxiv.org/abs/1404.7224),
  sections 2.2--2.3: the integrand, unit parallel setting, and locality.
- [Craig, *A gauge-invariant measure for lattice chiral fermions*](https://arxiv.org/html/2610.09093v1)
  and its [formalization archive](https://doi.org/10.5281/zenodo.23196062).
  In the inspected archive, `C02.lean` constructs native determinant exterior
  powers and uses the **measure** line `det(im P) ⊗ (det(im Q))*`. It is dual
  to the amplitude convention here. The archive uses Lean `4.35.0-rc2` and
  Mathlib `07b28b3a5d5b2c39c8b9f9377d0c3fcacb720e17`; those pins are not
  substituted for this repository's environment. Archive SHA-256:
  `761e06c05348d5984bf5e7064f5604113999b3cb56e5451856b4e44c071b9b89`.
