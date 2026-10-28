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
For every real `IsDualSeedPair X Y` with `X ≠ 0`, the proved corollary
asserts `D(X+Y) ≠ 0`; this is a conditional refutation, not an existential
counterexample theorem.

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

| Prerequisites | Consumers |
| --- | --- |
| `symmSandwich`, `symmDissipator`, `symmGenerator` | evaluation and inner-derivation cancellation |
| evaluation formulas | `dissipator_eq_double_commutator` |
| double-commutator identity | `dissipator_one`, `trace_dissipator` |
| square-zero seed equations | `sandwich_left`, `sandwich_right`, `anticomm_mul_left`, `anticomm_mul_right` |
| seed annihilation and native map linearity | `sandwich_add`, `sandwich_sub` |
| seed commutation and `sandwich_of_commute` | `sandwich_anticomm` |
| commutator anticommutation and native `Commute` transport | `sandwich_commutator` |
| sandwich images and commutation | corrected `dissipator_*` and `generator_*` actions |
| existing Peirce zero-product laws, `dissipator_add` | `dissipator_opposing_corners` |
| existing reflexive-seed multiplication laws | `support_mul_*`, normalized `dissipator_*_of_reflexive` |
| existing block definition and seed laws | `sandwich_peirceBlock`, `dissipator_peirceBlock` |
| block action formula | `dissipator_mem_block_range` |
| normalized sum action, native linearity, induction | `dissipator_iterate_add` |
| normalized sum action, existing `velocity_eq_zero_iff`, real nonzero scalar action | `real_dissipator_add_ne_zero` |

These prerequisite-to-consumer edges follow the actual proofs. Their
reflexive transitive closure is the proof-dependency partial order; no
ordering here denotes physical time or claims a fresh global declaration graph.

## Verification

[kernel_verified] and [axiom_audited] at the finite algebraic scope.

The focused [run 40724451618](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40724451618),
[job 122943810537](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40724451618/job/122943810537),
passed on 2026-10-28.

- Source commit: `ebca16d6064c97ffbf8bf1c4ed92e2ad0a6dd772`.
- Checked merge: `3dcc7adb613b098a698c64cfe31fa35808de6955`.
- Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
- Lean `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; dependency source,
  root toolchain and manifest pins remain unchanged.
- Command: `bash scripts/quality/check-square-zero-sandwich.sh`. The script
  builds all 23 project modules in the selected import closure serially into
  fresh project output files, using pinned mathlib dependencies and the shared
  build lock on an isolated GitHub runner.
- Exact-set axiom audit: all 41 declarations (38 theorems and three native
  linear-map definitions) use only `propext`, `Classical.choice`, `Quot.sound`.
- No source placeholders, custom axioms, `unsafe`, or `native_decide`.
  New modules produce zero Lean warnings. Shell syntax and diff checks pass.
- Existing imported owners emit 23 Lean warnings: 14 in `Singular/MoorePenrose`,
  two in `Core/JordanPeirceDecomposition`, seven in `Core/JordanAssociator`.
  These are deprecation/style/unused-argument warnings; the owners are unchanged.
- The semantic screen reports four warning-level `trivial_surface` findings:
  `symmSandwich_apply`, `symmDissipator_apply`, `sandwich_left`, `sandwich_right`.
  These are genuine evaluation and seed-annihilation lemmas used by subsequent
  proofs, not vacuous claims. No semantic-screen error is reported.
- Independent mathematical/source audit: PASS. Generation, source audit and
  acceptance roles are separate. Independent QA verdict: `accepted_limited_scope`,
  after directly verifying the final CI job, exact axiom inventory, source hashes
  and warning scope.

Focused kernel acceptance does not establish full-repository build success.
Style run `40723714903`, job `122941225781`, fails on the existing
`Physics/PellisFineStructure.lean` / `PellisfineStructure.lean` case collision.
Sorry Gate run `40723715167`, job `122941223653`, cannot find `lake` (exit 127),
before theorem checking. These failures were read directly from their logs.

The final evidence commit changes only this document; checked proof sources,
audit module, build script, workflow and dependency pins are unchanged.

### Verified source SHA256

- `SquareZeroSandwich.lean`: `8d5f642445e89e4ac01479d9c7afadbe66d96439e3308087d1ea95c48e9e87f5`.
- `PeirceSandwichAction.lean`: `bd2af0e49d60fe67ff94b84c1103bbf13798772349953070dbe388c99395a7f0`.
- `SquareZeroSandwichAudit.lean`: `df95a80c2819e2f36a41effc50b745efd948eebb7b0dfe85e8ab7494689021c2`.

## Open boundary

No Yang–Mills construction, mass gap, decay semigroup, spectral lower bound,
positivity, vacuum identification, or topological protection is asserted.
C is not generally scalar, globally central or idempotent. The four-element
span need not be four-dimensional or invariant without further hypotheses.
