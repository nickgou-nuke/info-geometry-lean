# Square-zero symmetric sandwich action

## Intake and exact scope

The original generated text is preserved without modification in
`docs/intake/2026-10-28-square-zero-sandwich.txt`.
SHA256: `f6e62981e5098032d6952a7f76dd62b02eb550c5c6a23a0a0101ad35ffc10277`.
Its claims of verification are intake, not accepted evidence.

Carrier: the full `Matrix n n R` for arbitrary finite `n`, with commutative
coefficient ring `R`; matrix multiplication is not assumed commutative.
Real specialization uses `R = ℝ`. No complexification, coordinate substitute,
diagonalization, positivity or adjoint identification is introduced.

For X²=Y²=0, let C=XY+YX, E=X+Y, J=X-Y, S=XY-YX.
Define native R-linear maps Φ(Z)=XZY+YZX and
D(Z)=2•Φ(Z)-(CZ+ZC). Prove D equals the negative symmetric double
commutator on all matrices. Prove Φ(C)=C², Φ(E)=Φ(J)=0, Φ(S)=-CS;
D(1)=D(C)=0, D(E)=-2•(CE), D(J)=-2•(CJ), D(S)=-4•(CS).
C commutes with both seeds, hence with E,J,S. Addition of [C,-]
therefore leaves these particular actions unchanged.

The intake assertions Φ(E)=CE, Φ(J)=-CJ, D(E)=0 and D(J)=-4CJ are
false in general. Under the existing additional reflexivity equations
XYX=X and YXY=Y, the corrected actions become -2E,-2J,-4S.
The real nonzero-seed corollary will formally refute D(E)=0.

## Owner search and reuse

- `Core.PeirceDecomposition`: the four actual Peirce components.
- `Core.PeirceDecomposition.peirce10_mul_peirce10_eq_zero` and
  `peirce01_mul_peirce01_eq_zero`: opposing idempotent corners are square-zero,
  without reflexivity. These supply the input adapter.
  `Core.PeirceGrading.corners_sq_zero` was also inspected.
- `Core.DualSeedPeirce.IsDualSeedPair`: exactly X²=Y²=0, XYX=X, YXY=Y;
  existing `pd`, `qd`, `pb`, `qb`, `pp`, `pq`, `qp`, `qq` multiplication laws.
- `Core.PeirceRotor.peirceBlock` / `peirceBlock_mul`: actual supported operators.
- `Core.DiracSuperalgebra` / `Singular.SquareZeroChiralHodge`: support
  expressions inspected; Moore–Penrose hypotheses are not silently imported
  into the weaker square-zero claim.
- `Modular.GKSLDissipatorAlgebraic`: star-based map differs from arbitrary
  paired sandwich; no claim that Φ is a completely positive map is made.
- `Canonical.MatrixTwoNoncommutativity`: imported native noncommutativity witness.
- Native mathlib `LinearMap`, linearity/composition, matrix multiplication,
  and module identities provide the new operator surface.

Repository-wide lexical search and `context_preflight.py` were run; the
local declaration graph artifacts are absent, and no graph freshness is claimed.
Categorical owner map and tensor/colimit interfaces were inspected as scope
boundaries; this is finite algebra, with no colimit assertion.

## Dependency order

1. Native sandwich/dissipator maps and their evaluation formulas.
2. Square-zero seed action and commutation with the anticommutator.
3. Sandwich actions on C,E,J,S and the corrected dissipator actions.
4. Existing opposing-corner nilpotency supplies the geometric specialization.
5. Existing reflexive-seed multiplication laws normalize the actions.
6. Native linearity transports the action to supported Peirce blocks.
7. Nonzero real seeds refute the claimed stationary sum.

Only actual prerequisite edges will be reported in final verification.
No ordering here denotes physical time.

## Verification

Pending kernel check, exact-set axiom audit, and independent source/QA review.
The generation, audit and acceptance roles are separate.

## Open boundary

No Yang–Mills construction, mass gap, decay semigroup, spectral lower bound,
positivity, vacuum identification, or topological protection is asserted.
C is not generally scalar, globally central or idempotent. The four-element
span need not be four-dimensional or invariant without further hypotheses.
