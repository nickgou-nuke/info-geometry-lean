# Operator-valued Clifford coordinates and star-form symmetries

## Intake and implementation base

The intake is `Pasted text(20261112-173814).txt`, received on 2026-11-12.
It proposes noncommutative connection curvature, Clifford matrix relations,
Peirce parity, four-coefficient Walsh reconstruction and star-form squeezes.
The implementation base is `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
Lean and Mathlib pins are unchanged.
The intake SHA256 is
`b91f747c5cf2a9a6cb9d05dc6aff5f760072e1a64a7579e0c90d59d59dd8c5ed`.

## Existing owners and reuse

* `Geometry.AssociativeGaugeConnection.curvature_action` already derives
  curvature from globally Leibniz native linear endomorphisms.
  `OperatorAlgebra.DerivationGaugeTransport` includes the noncommuting-base
  connection commutator. A connection is not generally a ring derivation.
* `InfoGeometry.OperatorAlgebra.LieJordan.lie_lie`, in module
  `OperatorAlgebra.LieJordanEndomorphisms`, owns the inner-derivation
  commutator identity.
* `Algebra.PeirceDeWittChiralSplit` and `Algebra.PeirceParityClosure` own the
  four-corner split, parity projections, uniqueness, product laws and grading
  conjugation on arbitrary rings. `PeirceParityTorsion` records the obstruction
  to converses in characteristic two. These broader parity owners were
  inspected as prior art; the selected native check uses the direct
  `Algebra.IdempotentProjector` owner needed by the new Peirce lift.
* `Clifford.OperatorValuedJones` owns `I_mat`, `Gamma_mat`, `J_mat`, `K_mat`
  and `reconstruct_jones`. Its `J_mat` is the intake's shift and its `K_mat`
  is the negative of the intake's skew generator. These signs are retained.
* `Canonical.IntegralChiralCliffordOrder` already identifies the integral
  four-generator order with the parity subring and proves its additive index
  is four. This is inspected prior art, not part of the new selected build.

The new implementation extends the existing native matrix synthesis. It does
not duplicate the attachment's curvature and parity APIs.

## Four-coefficient reconstruction

For arbitrary `Ring B`, synthesis is the existing ordered operator-valued map

\[
S(a,b,c,d)=\begin{pmatrix}a+b&c+d\\c-d&a-b\end{pmatrix}.
\]

The corresponding extraction is

\[
T(M)=(M_{00}+M_{11},M_{00}-M_{11},M_{01}+M_{10},M_{01}-M_{10}).
\]

The targets are the two identities `S(T(M))=2M` and `T(S(v))=2v`, and a native
linear equivalence when `[Invertible (2 : B)]`. Normalization places the
inverse of two on the right, preserving left `B`-linearity without assuming
commutative coefficients. The Peirce fiber lift is connected explicitly to
the diagonal embedding of the compressed `(0,0)` coefficient.

Over the integers, the four displayed generators do not span all matrices:
synthesizing `E00` would require `2a=1`. In characteristic two the grading
collapses to the identity and the skew generator equals the shift. Thus the
unnormalized identity must not be called an unconditional inverse or basis.
No integral diagonal-Clifford tensor isomorphism is asserted. The finite
coordinate map is not an analytic Mellin transform, and the sign group is not
the unit group of `ZMod 2`.

## Internal twists

For any coefficient `j : B` with `j * j = -1`, entrywise left multiplication
changes the exchange square to `-1` and the skew square to `1`:

\[
(j\mathbin{\bullet}J)^2=-I,\qquad
(j\mathbin{\bullet}(-K))^2=I.
\]

Both twisted generators anticommute with the grading, and they anticommute
with each other. These anticommutation statements need no assumption on the
square or centrality of `j`. Commutation with an arbitrary scalar fiber has
an exact boundary: `Matrix.scalar a` commutes with either twisted generator
if and only if `a` commutes with `j`. This does not identify the full
coefficient algebra with a commuting tensor factor.

## Star-form Lie algebra and group

For an arbitrary `Ring A` with `StarRing A` and a fixed `j : A`, construct

\[
\mathfrak g_j=\{x:\star(x)j+jx=0\}
\]

as a native `LieSubalgebra ℤ A`. The integer scalar ring preserves the
noncommutative coefficient algebra. Also construct

\[
G_j=\{u\in A^\times:\star(u)ju=j\}
\]

as a `Subgroup Aˣ`; invertibility is part of the carrier, and subgroup closure
is proved. A one-sided form equation alone is insufficient to infer a unit
over general operator rings.

Specialize to `Matrix (Fin 2) (Fin 2) B`, conjugate transpose, and
`Ω = -OperatorValuedJones.K_mat`. Prove the exact block characterization

\[
X\in\mathfrak g_\Omega\quad\Longleftrightarrow\quad
X_{11}=-\star X_{00},\quad
\star X_{01}=X_{01},\quad\star X_{10}=X_{10}.
\]

For each `u : Bˣ`, the matrix

\[
S(u)=\operatorname{diag}(u,\star(u^{-1}))
\]

has explicit inverse `S(u⁻¹)`, preserves `Ω`, and defines an injective native
group homomorphism into `G_Ω`. Multiplicativity follows from the two order
reversals of inversion and star; no commuting-unit premise is introduced.

The unstarred `Θ(u)=diag(u,u⁻¹)` satisfies the lifted clock/shift identity and
shift inversion. Its multiplicativity holds precisely for commuting inputs.
It is not presented as a group homomorphism on arbitrary noncommuting units.

## Boundaries and verification

The Peirce grading here is not an identification with the spacetime DeWitt
quadratic form. Internal square-sign reversal is a ring identity and does not
supply a real quadratic signature or positivity. The arbitrary-ring setting
has no exponential or convergence assumptions. No optical, gauge-field,
mass, analytic completion or tensor-colimit consequence is inferred.

The selected validation target is
`InfoGeometry.Canonical.CliffordPeirceWalshAudit`. It imports the two new
owners and audits every declaration, including private and generated
declarations, in those owners and four reused owners:
`OperatorValuedJones`, `IdempotentProjector`, `AssociativeGaugeConnection`,
and `LieJordanEndomorphisms`.
Accepted axiom dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. Independent source review and
independent native QA are separate from author checks. Exact final results
belong in the accompanying verification record; this contract is not a build
certificate. Root publication gates remain separate from selected compilation.
