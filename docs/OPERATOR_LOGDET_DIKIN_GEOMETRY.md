# Operator logdet, Dikin geometry, and relative deformation

## Theorem contract

This development continues PR #241 from commit
`4e2c0ef69aced9dee6290d2c798940a704f893f4`. Its carriers are full complex
matrix algebras, their native self-adjoint and strictly-positive loci, and
the repository's full finite bounded-operator algebra.

The source investigation identified three existing, distinct constructions:

* `Canonical.FiniteBogoliubovFrameDeformationEntropy`: arbitrary invertible
  current/reference frames give `E = current * vacuum⁻¹`, the strictly positive
  polar operator `P = CFC.abs E`, and the self-adjoint `K = -CFC.log P`.
  The owner proves `exp (-K) = P` and `Re (trace K) = -log ‖det E‖`.
* `Analysis.LogDetSelfConcordantBarrier` and
  `Analysis.MatrixSpectralSelfConcordantBarrier`: ordered real-matrix trace
  forms and their spectral third-order inequality, with supplied conjugation
  and spectral data. Their definitions alone do not identify native derivatives.
* `Canonical.DikinFiniteOrbitColimit`: the genuine BKM quadratic form and
  ellipsoid conditions on `selfAdjoint (FiniteOperatorAlgebra n)`, with
  faithful density and explicit continuity of its power path.

## New theorem owners

All new statements use native Mathlib matrices, continuous linear maps,
`fderiv`/`deriv`, CFC, the positive matrix order, and the repository's genuine
Kubo--Mori integral. There are no new assumed derivative, spectral, or
containment certificate fields.

| Owner | Mathematical responsibility |
| --- | --- |
| `Analysis.ComplexMatrixJacobi` | Complex determinant calculus in arbitrary matrix directions |
| `Analysis.ComplexMatrixLogDetCalculus` | Native smoothness at every order, actual real first and second Fréchet derivatives, iterated line derivatives, and singular-boundary divergence |
| `Analysis.PositiveMatrixDikin` | Internally constructed spectral bounds, actual inverse-square-root normalization, positive quadratic form, and Dikin order/containment bounds |
| `Canonical.PolarFrameTraceDensity` | Faithful positive trace-density functionals, uniqueness, trace normalization, and the central logarithmic shift |
| `Canonical.OperatorLogDetDikinGeometry` | Identification with the existing native `hessianMap`; self-concordance and Dikin theorems for the relative frame's polar operator |
| `Canonical.BKMCommutatorDikin` | Genuine BKM energy of the self-adjoint rotation of a commutator; zero and positive energy characterizations |
| `Canonical.PolarFrameBKMGeometry` | Explicit matrix/operator transport and invariance of the BKM commutator geometry under polar trace normalization |
| `Canonical.OperatorLogDetDikinGeometryTests` | Exact native derivative values and cone containment for a concrete noncommuting matrix pair |

## Proved connections

1. Differentiate a scalar logdet readout on the full complex matrix algebra
   using native Mathlib calculus. Identify actual second and third additive
   variations with ordered inverse/trace formulas. Invertibility, real versus
   complex differentiation, and derivative order remain explicit in the types.
2. Derive the spectral third-order inequality for every Hermitian complex
   matrix from its native spectral theorem. Supply the inverse-square-root
   conjugation from the actual strictly positive base operator.
3. Prove that a subunit logdet Dikin variation stays in the strictly positive
   cone. No containment estimate or diagonalization may be assumed as a
   structure field.
4. Apply this geometry to the existing strictly positive polar distortion
   of arbitrary invertible relative frames, preserving the original operator
   and its determinant/trace readout.
5. Connect the existing BKM ellipsoids to commutator geometry through the
   genuine self-adjoint operator `i • (X * Y - Y * X)`. Prove its zero-radius
   and positive-energy characterizations with full noncommutative inputs.
6. Realize a strictly positive polar matrix as the unique density of a
   faithful positive linear functional relative to the ordinary matrix trace.
   Prove trace normalization and its central logarithmic correction, then
   transport the preserved commutators into the existing BKM operator carrier.

### Actual derivatives and the positive cone

For a full complex matrix `A`, define

\[
F(A)=-\log\lVert\det A\rVert.
\]

The potential is natively `ContDiffAt` to every differentiability order at
every invertible `A`. Its actual real Fréchet derivatives satisfy

\[
DF_A[H]=-\operatorname{ReTr}(A^{-1}H),\qquad
D^2F_A[K,H]=\operatorname{ReTr}(A^{-1}KA^{-1}H).
\]

The actual third derivative of the additive line is

\[
\left.\frac{d^3}{dt^3}F(A+tH)\right|_{t=0}
=-2\operatorname{ReTr}((A^{-1}H)^3).
\]

Derivatives of the derivative fields are justified by equality throughout an
open neighborhood of invertible matrices, rather than equality only at the
base point. The boundary theorem sends `F(X)` to `+∞` whenever `X` tends to a
singular matrix through eventually invertible matrices.

For `P` strictly positive and `H` self-adjoint, put

\[
B=P^{-1/2}HP^{-1/2},\qquad q=D^2F_P[H,H].
\]

CFC constructs `P⁻¹ᐟ²`; cyclic trace gives `q = ReTr(B²)`, and Mathlib's
Hermitian spectral theorem is applied internally to `B`. The resulting native
theorems prove

\[
q\ge0,\quad q=0\iff H=0,\quad
\left|\left.\frac{d^3}{dt^3}F(P+tH)\right|_{t=0}\right|\le 2q^{3/2},
\]

\[
|DF_P[H]|\le\sqrt{\operatorname{card}(n)}\sqrt q,
\qquad (1-\sqrt q)P\le P+H\le(1+\sqrt q)P,
\]

and `q < 1` implies `IsStrictlyPositive (P + H)`. The capstone states these
facts using the pre-existing `Geometry.LegendreDifferential.hessianMap`.

### Trace-relative density and deformation

Every positive `P` defines a native positive linear map

\[
\varphi_P(X)=\operatorname{Tr}(PX).
\]

The proof uses the actual congruence
`Tr(PX) = Tr(sqrt(P) X sqrt(P))`. For strictly positive `P`, this functional
is faithful on positive inputs. Equality of the functionals on the full
matrix algebra implies equality of their density matrices.

For a nonempty finite index type, `Z = ReTr(P) > 0` and `ρ = Z⁻¹P` is
strictly positive with trace one. Native CFC proves

\[
-\log\rho=-\log P+(\log Z)I.
\]

For the original arbitrary invertible relative frame `E`, take `P=|E|`.
The existing `K=-log P` is preserved, and the trace identities become

\[
F(P)=\operatorname{ReTr}(K)=-\log\lVert\det E\rVert,\qquad
\operatorname{ReTr}(-\log\rho)
=-\log\lVert\det E\rVert+\operatorname{card}(n)\log Z.
\]

This is the finite matrix density relative to the ordinary trace. It does
not assert a measure-theoretic Radon--Nikodym identity or an identification
with a left/right relative modular endomorphism.

### BKM commutator geometry and normalization

For native self-adjoint bounded operators `X,Y`, set `C=XY-YX` and `J=iC`.
The genuine integral BKM pairing is invariant under simultaneous multiplication
of both inputs by `i`. Thus

\[
q_D^{\mathrm{BKM}}(J)
=g_D(C,C)
=\operatorname{Cov}^{\mathrm{centered\,BKM}}_D(C,C).
\]

This value is zero exactly when `X` and `Y` commute, and strictly positive
exactly when they do not. The corresponding zero-radius ellipsoid condition
is also equivalent to commutativity. Centering fixes the original skew-adjoint
`C`; it need not fix the rotated self-adjoint `J`.

The central shift `-log ρ = -log P + log(Z) I` preserves every commutator.
`PolarFrameBKMGeometry` transports this equality through the existing
`matrixOp`/`matrixOfOp` realization, then proves equality of commutator BKM
energies and ellipsoid conditions **at the same faithful density `D`**.

## Dependency order

* native determinant and inverse calculus → actual logdet variations;
* native Hermitian spectral theorem → trace-power inequality;
* strict positivity → CFC inverse square root → normalized variation;
* normalized variation + trace bound → positive-cone Dikin containment;
* actual variations + trace-power inequality → self-concordance estimate;
* invertible relative frames → positive polar distortion → the preceding
  positive-cone theorems and the existing deformation-surprisal readout;
* faithful BKM + adjoint commutator + phase invariance → operator Dikin
  commutator-energy and zero-radius characterizations.
* positive polar distortion → faithful trace density → trace normalization
  → central logarithmic shift → preserved bounded-operator commutators
  → preserved BKM energies and ellipsoid conditions at fixed density.

## Concrete noncommutative check

The exact kernel-checked example uses

\[
P=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
H=\tfrac14\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
\]

Both matrices have off-diagonal entries, and the file explicitly proves
`¬ Commute P H`. It constructs strict positivity from the Gram identity
`P - I = Rᴴ * R` with `R=[[1,1],[0,0]]`, and proves
the actual inverse. The native derivative checks are

\[
D^2F_P[H,H]=\frac19,\qquad
\left.\frac{d^3}{dt^3}F(P+tH)\right|_{t=0}=\frac{11}{216}.
\]

The positivity of `P+H` is then deduced from the new Dikin containment theorem.

## Boundaries

Self-concordance concerns a real-valued potential in a specified affine
coordinate on the positive cone. The nonlinear polar map from arbitrary
frames is not asserted to preserve its Hessian or self-concordance constant.
The Gibbs log-partition Hessian, centered BKM covariance, logdet Hessian, and
Peirce curvature retain their distinct definitions. A measure RN density,
relative frame unit, and left/right modular endomorphism are not identified
without an explicit map and compatibility theorem.

No smoothness, spectral decomposition, derivative formula, or cone containment
is to be hidden in a new certificate field. Standard hypotheses such as
invertibility, strict positivity, Hermitian directions, and continuity of
the existing BKM power path are retained.

The self-concordance estimate uses the ordinary, unnormalized trace. Trace
normalization of the density does not divide the barrier potential by the
dimension. The BKM quadratic form and logdet Hessian retain their distinct
definitions. No BKM positive-cone containment statement is inferred merely
from the word "ellipsoid".

## Verification

Independent verification passed with Lean **4.34.1**, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and the repository-pinned Mathlib
revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

* **31 repository source modules** rebuilt from a fresh copied import closure.
* **8 new owners; all 250 owned declarations** accepted by the native audit,
  including private and compiler-generated declarations. The number 250 is
  a declaration count, not a count of named mathematical theorems.
* Transitive axioms: exactly `[propext, Classical.choice, Quot.sound]`.
  No disallowed axiom, unsafe declaration, or partial declaration passed the
  complete-owner audit.
* **Zero warnings in every new owner.** Existing dependencies emitted 22
  notices: 8 deprecation notices, 6 unused-simp arguments, and 8 tactic-style
  suggestions. The fresh run contained no placeholder/proof warnings.
* The concrete noncommuting example compiled with its exact native Hessian,
  third derivative, inverse, and containment proofs.
* All 31 source hashes matched after verification, and their Git blob hashes
  matched the staged source tree before publication.

The [verification manifest](verification/operator_logdet_dikin_geometry_20261028.json)
records the actual acyclic import graph, source SHA-256 and Git blob hashes,
per-module results, pinned tools, and declaration counts. The [native audit
output](verification/operator_logdet_dikin_geometry_axioms_20261028.txt)
records every audited declaration and the final axiom set. The working-tree
base identifies the ancestor; the source hashes identify the exact additions
verified for this PR.

### Reproduce

With the pinned Lean toolchain and a Mathlib checkout at the exact manifest
revision, run:

```bash
python tools/quality/check_operator_logdet_dikin.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/new-verification-directory \
  --fetch-cache
```

The output directory must be new. The checker enforces the shared build lock,
excludes existing project oleans, compiles every repository dependency from
copied source, and runs the complete-owner native audit. The eight selected
owners receive the declaration audit; imported existing owners are compiled
as dependencies. Whole-repository downstream compatibility is outside this
verification scope. The scoped GitHub workflow runs the same command and
uploads the logs, exact source snapshot, and machine-readable result.
