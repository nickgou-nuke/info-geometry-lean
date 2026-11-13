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

## Planned mathematical owners

1. **Transpose-compatible adjoint.** Construct the head anti-involution by
   pulling real matrix transpose back through `cl11StandardEquiv`. Construct
   the graded tensor anti-involution by pulling matrix conjugate transpose
   back through the existing native equivalence. Prove additivity, real
   scalar compatibility, involutivity, reversed multiplication, and the
   homogeneous Koszul sign. Coefficient star must commute with coefficient
   parity. Mathlib's canonical Clifford star is a different convention;
   no global instance is overwritten. Algebraic star alone gives no positivity.
2. **Underlying real cut rank.** Construct canonical tensor contraction to
   maps from the left dual. Define rank as the dimension of its range, with
   finite left factor and unrestricted right factor. Construct a controlled
   parity tensor map, prove it is involutive, and prove both factor-two rank
   inequalities. A finite right-dimension bound requires an explicit finite
   dimensionality assumption. This is not a new TT minimality theorem.
3. **Finite real dimension.** Prove invertible anticommuting operators force
   even real dimension, and odd dimension forces a reversed operator to be
   singular. Exhibit a reversing pair on three real coordinates whose
   reversed operator is not tripotent. Odd external matrix size over an
   arbitrary operator coefficient algebra is not a dimension obstruction.
4. **Projector defects.** Preserve the valid two-factor half-square identity;
   refute the proposed all-length scaling at three factors on an actual
   noncommutative Clifford carrier. State corrected sufficient hypotheses
   rather than the false iff between idempotence and every factor being even.

All planned owners require complete native Lean proofs before promotion.
Candidates are not kernel evidence. Exact source closure compilation,
owned-declaration axiom auditing, independent semantic review, staged proof
gate, and root quality gates remain separately reported acceptance surfaces.

## Source claims that cannot be promoted as written

- The universal formula `(P₀^⊗̂n)² = 2^{-(n-1)} P₀^⊗̂n` fails at `n = 3`.
- Even boundary labels in a homogeneous super-TT force total-even parity.
  They do not represent arbitrary matrices or inhomogeneous projectors.
- A controlled parity twist preserves rank on fixed-total-parity tensors;
  rank doubling concerns inhomogeneous tensors.
- `JSJ⁻¹ = -S` in odd real dimension implies singularity, not `S³ = S`.
- An odd outer index in `M_r(B)` does not exclude a matrix factor inside `B`.
- The quartet's tensor-lattice index is `4^(n * 4^(n-1))`, not `4^n`.
- A concrete inner-grading untwist is not by itself a universal bosonization
  or monoidal trivialization of superalgebras.

## Actual dependency order

Graded coefficient algebra and the concrete Clifford frame feed the existing
native head equivalence. That equivalence feeds adjoint transport and concrete
projector calculations. Tensor contraction and parity projections independently
feed cut-rank bounds. Determinants independently feed the dimension obstruction.
Tripotent geometry needs an additional tripotence hypothesis. No dependency is
inferred solely from the source's numbered conceptual chain.
