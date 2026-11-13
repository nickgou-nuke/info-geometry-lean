# Graded Clifford star, parity cut rank, and dimension boundaries

## Frozen intake and scope

The source is `Pasted text(20261113-100758).txt`, 24,406 bytes, SHA-256
`f21693468fc1ff3ff5ed07361d18f0f65c8461a090ac2ce8c6d7f480f1ce17c4`.
It has 136 logical lines, no terminal newline, and ends during Deduction D2
after `K^{q_r^{\mathrm{tot}}} a_r`. No missing continuation is inferred.

This task extends the stable arbitrary-graded-coefficient owner in PR #338,
commit `ce34c806983f97e7ff3c95b5d06081bd93534c5b`. The distinct intake and
active recursive-unrolling work in PR #354 are not modified. Completed
tripotent PR #352 and matrix-decomposition PR #349 are not modified.

## Exact owner reuse

`InfoGeometry.Clifford.Cl11GradedTensorMorita.tensorMatrixEquiv` is the
native algebra equivalence from `CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜`
to `Matrix (Fin 2) (Fin 2) A`. Its hypotheses are `[Ring A] [Algebra ℝ A]`,
a native `ZMod 2` grading, and an algebra automorphism acting by +1 on the
even component and −1 on the odd component. It imposes no commutativity or
finite-dimensionality on `A`. Its lift, explicit inverse, and product parity
are reused, not assumed or reconstructed.

The existing faithful standard head representation uses a Walsh change of
basis. Positive and negative Clifford generators map to `J1` and `-Eminus`;
the even grading implementer maps to `Eplus`. These are conjugate to the
intake's quartet, and the signs and order are retained explicitly.

## Implemented mathematical owners

The six source owners below are kernel checked at published commit
`ec36632a52860b8e710cd6b1c258a5c6f649d06e`, tree
`21b365c94f4e44fb853d342c7f7ecc04f07be35b`. All 44 modules in their exact
repository-local source closure compiled, and the native ownership audit passed
for all 197 declarations belonging to the six owners, including private and
generated declarations. The only observed axioms were `propext`,
`Classical.choice`, and `Quot.sound`. Independent QA reconciled every source
hash and all declaration counts against the successful run. See the
[acceptance evidence](evidence/graded-clifford-star-rank/README.md) for exact
commands, hashes, warnings, and the separate root-integration limitation.

1. **Transpose-compatible adjoint** (`Cl11GradedAdjoint.lean`). Construct the head anti-involution by
   pulling real matrix transpose back through `cl11StandardEquiv`. Construct
   the graded tensor anti-involution by pulling matrix conjugate transpose
   back through the existing native equivalence. Prove additivity, real
   scalar compatibility, involutivity, reversed multiplication, and the
   homogeneous Koszul sign. The parity-compatibility and homogeneous-sign
   theorems explicitly assume that coefficient star commutes with coefficient
   parity; construction of the transported anti-involution does not need that
   extra hypothesis. Mathlib's canonical Clifford star is a different convention;
   no global instance is overwritten. Algebraic star alone gives no positivity.
2. **Underlying real cut rank** (`GradedTensorCutRank.lean`). Construct canonical tensor contraction to
   maps from the left dual. Define rank as the dimension of its range, with
   finite left factor and unrestricted right factor. Construct a controlled
   parity tensor map, prove it is involutive, and prove both factor-two rank
   inequalities. A finite right-dimension bound requires an explicit finite
   dimensionality assumption. This is not a new TT minimality theorem.
3. **Actual untwist application** (`Cl11UntwistCutRank.lean`). Independently
   construct ordinary tensor/matrix coordinates with Mathlib tensor algebra
   equivalences. Prove that the existing native graded lift agrees with those
   coordinates after the controlled parity twist. Thus both rank inequalities
   apply to the actual one-head Clifford untwist, not only an abstract map.
   The left involution is right multiplication by the native Clifford volume.
   This application retains arbitrary, possibly infinite-dimensional,
   noncommutative real coefficient algebras.
4. **Finite real dimension** (`FiniteRealAnticommutation.lean`). Prove invertible anticommuting operators force
   even real dimension, and odd dimension forces a reversed operator to be
   singular. Prove the basis-independent endomorphism versions and the
   even-dimensional obstruction to a real square root of minus the identity.
5. **Explicit boundary counterexamples** (`GradedUnrollingCounterexamples.lean`).
   Exhibit a reversing pair on three real coordinates whose
   reversed operator is not tripotent. Odd external matrix size over an
   arbitrary operator coefficient algebra is not a dimension obstruction.
6. **Projector defects** (`Cl11GradedProjectorDefects.lean`). Preserve the valid two-factor half-square identity;
   refute the proposed all-length scaling at three factors on an actual
   noncommutative Clifford carrier. Prove universal ordered-word identities
   before specializing to Mathlib's weighted `Cl(3,3)` quotient. Detect nonzero
   defects through one entry of the existing Jordan--Wigner representation;
   the argument neither assumes that representation is injective nor treats
   entry evaluation as multiplicative.

Exact source closure compilation, owned-declaration axiom auditing,
independent semantic review, the staged proof gate, and root quality gates
are separate acceptance surfaces. The first two passed at the exact revision
above; this does not establish whole-repository integration. The unchanged
incremental and full root gates encounter a missing required
`external_refs/homotopy-hypothesis-lean4` package before root compilation.
Earlier failed checkpoints remain labeled as failures in the evidence.

## Exact equations and carrier boundaries

For homogeneous head and coefficient elements of degrees `i,j : ZMod 2`,
the transported tensor adjoint satisfies

```text
(x graded-tensor a)^dagger = (-1)^(i*j) (headAdjoint x graded-tensor star a).
```

The tensor algebra is the native graded tensor product. The target matrix
operation is conjugate transpose in the full coefficient star algebra. No
positivity, norm, analytic completion, or replacement global star instance is
introduced.

For a finite-dimensional real left factor `V`, cut rank is

```text
r(t) = finrank(range(contraction(t) : Dual(V) -> W)).
```

The right factor `W` can be infinite-dimensional. For real linear involutions
`theta` and `T` (both squares equal `id`), construct the parity projections
`p0=(id+theta)/2`, `p1=(id-theta)/2`. Then

```text
C = id tensor p0 + T tensor p1,
C(C(t)) = t,
r(C(t)) <= 2*r(t),
r(t) <= 2*r(C(t)).
```

The application uses `V=CliffordAlgebra q11` and `T(x)=x*J1_cl`. Both real
coordinate systems are independently defined before proving the identity
relating them. The head bound is `r <= 4`; a finite right-tail bound requires
explicit finite-dimensionality of both its ordinary factor and its operator
coefficient algebra.

Let `x,y,z` be the three positive basis generators in the native `Cl(3,3)`
owner, and retain their displayed order. With

```text
q2 = (1+x)(1+y),
q3 = (1+x)(1+y)(1+z),
w3 = (1+x)y(1+z),
p2 = q2/4, p3 = q3/8,
```

the exact identities are `q2^2=2*q2`, `q3^2=4*w3`, and `p2^2=p2/2`.
The represented all-zero matrix entry of `p3^2-p3/4` is `-1/32`, directly
refuting the source's normalized three-site scaling. The ordinary idempotence
defects of both `p2` and `p3` have entry `-1/8`. Each single-site factor is
idempotent, and the first two factors are proved not to commute.

The finite real dimension owner assumes only invertibility and
anticommutation, not involutivity. Its determinant proof does not commute the
operators; it commutes their real determinant values after applying the
determinant. The explicit three-dimensional counterexample has
`S=diag(2,-2,0)` and an invertible reversing involution. It is singular but not
tripotent. A separate anticommuting unit pair in `M3(M2(R))`, transported by
Mathlib's matrix flattening equivalence, acts on six real coordinates.

## Source claims that cannot be promoted as written

- The universal formula `(P₀^⊗̂n)² = 2^{-(n-1)} P₀^⊗̂n` fails at `n = 3`.
- Even boundary labels in a homogeneous super-TT force total-even parity.
  They do not represent arbitrary matrices or inhomogeneous projectors.
- For the Clifford twist, whose left involution preserves parity, fixed-total-parity
  tensors retain their rank; rank doubling concerns inhomogeneous tensors. This
  statement is not asserted for an arbitrary left involution that changes parity.
- `JSJ⁻¹ = -S` in odd real dimension implies singularity, not `S³ = S`.
- An odd outer index in `M_r(B)` does not exclude a matrix factor inside `B`.
- The quartet's tensor-lattice index is `4^(n * 4^(n-1))`, not `4^n`.
- A concrete inner-grading untwist is not by itself a universal bosonization
  or monoidal trivialization of superalgebras.

## Explicitly unproved extensions

This PR does not claim a completed arbitrary-length graded-terminal unrolling,
all cuts of a graded tensor train, TT existence/minimality, fixed-total-parity
rank equality, sharpness of the factor-two bound, the integral lattice-index
theorem, or analytic positivity. The corrected sufficient condition that
even idempotent factors give an idempotent graded tensor is explained by the
intake audit but is not promoted as a new theorem here. The false converse is
not used. Existing recursive work for a purely even terminal algebra remains
owned by the separate PR #354.

## Actual dependency order

Graded coefficient algebra and the concrete Clifford frame feed the existing
native head equivalence. That equivalence feeds adjoint transport and the
one-head rank bridge. Tensor contraction and parity projections independently
feed cut-rank bounds. The projector defects use the native weighted Clifford
relations and the existing Jordan--Wigner algebra representation. Determinants
independently feed the dimension obstruction.
Tripotent geometry needs an additional tripotence hypothesis. No dependency is
inferred solely from the source's numbered conceptual chain.
