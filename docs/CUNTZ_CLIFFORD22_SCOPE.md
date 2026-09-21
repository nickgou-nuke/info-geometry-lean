# Cuntz matrix units, real Cl(2,2), and clock/trace scope

## Input and owner reuse

The supplied audit asks for algebraic repair, not a proof of the physical
claims it rejects. This change reuses `Algebra.CuntzMatrixUnits` and the
underlying `Algebra.CuntzTensorQuotient`; it does not redefine Cuntz generators.
The coefficient carrier is the existing algebraic quotient with scalars
restricted from C to R. This is not a construction of the norm-complete C*
algebra O_2. In particular, the inherited formal dagger in that owner fixes
complex scalars; no conjugate-linear C*-adjoint claim is made for the quotient.
The displayed split generators use only real coefficients.

## Implemented algebra

Set u=E01+E10, v=E00-E11, w=E01-E10. Their squares are 1,1,-1 and their pairwise
anticommutators vanish. The corrected block matrices have signature +,+,-,-.
All sixteen relations are proved parametrically. More importantly, the full
linear combination satisfies the quadratic relation, and `CliffordAlgebra.lift`
constructs an actual real algebra homomorphism. The images of the four native
generators are identified with the displayed blocks. Faithfulness and a
C*-completion are not claimed.

The old single-isometry block squares to diag(E00,1), and is not square-one in
any nontrivial realization. The explicit hypothesis 1 != 0 is retained rather
than silently assuming a nontriviality theorem for the quotient.

The other module proves that left and right multiplication commute, that an
invertible commuting Weyl pair has scalar q=1, and that the Weyl commutator
and anticommutator have coefficients 1-q and 1+q respectively. It also proves
that no additive cyclic functional on the two-generator Cuntz quotient can
have value 1 at the identity. This does not rule out KMS states, non-finite
weights, or traces on finite matrix subalgebras.

## Deliberately separate claims

No identification of Tomita conjugation with a linear Krein symmetry is made.
No connection, torsion, Chern--Simons action, spectral map to zeta zeros,
chronon, galactic potential, CMB prediction, or Navier--Stokes continuation is
asserted. In particular, these algebraic results cannot replace the spatial
coercivity/reconstruction obligations recorded in the supplied fluid review.
The finite cubic-clock spectrum and logarithmic-derivative residue in the
source audit are not inferred from these Clifford relations.

## Verification

`CuntzClifford22Audit.lean` prints the axiom dependencies of eight principal
results. `tools/quality/check_cuntz_clifford22.py` stages the exact reachable
owner sources into a fresh package, uses the immutable Mathlib revision from
the root manifest, and uses that revision's own compiler. It does not change
any root dependency or compiler pin and does not initialize workstation-only
submodules. The repository build lock is held for sequential checking.

The evidence records the root compiler and checked compiler separately. A
successful narrow source check is not a successful full-root package build.
At authoring time the root requests Lean 4.28.1. The compiler for the pinned
Mathlib source must be read from that exact revision; no binary-compatibility
assumption is made. Check the attached CI evidence for the actual result.
