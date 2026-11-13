# Tripotent grading, involution and corner-generation contract

## Intake and baseline

The verbatim Bulgarian intake is preserved in
`docs/intake/tripotent_krein_morita_20261113.txt` (SHA-256
`91f298d175b92810a214d6696f4a4a588c2fa231ee5058449a8a74c0bf89d2c8`,
44,529 bytes). It is a proposed synthesis, not evidence of completed proofs.
The implementation starts from PR #323 at
`c23aa651772224079271a35a0acca5a3f9767354`, with unchanged root Lean and
Mathlib pins. This branch is stacked on that source, not a claim that #323
has merged.

The carrier is the original arbitrary unital associative real algebra `A`.
Integer components are the existing `InfoGeometry.Physics.Algebra.adGrade S k`.
Operator kernel statements use the actual `Module.End ℝ V` action on `V`.
No scalar, diagonal or commuting replacement of the noncommutative carrier
is used. Tripotence is `S * S * S = S`; any of the five grades may vanish.

## Source owners and dependency order

Existing Peirce projectors, five ranges, eigenspace identification, quintic
annihilator, adjoint rigidity, parity and associative signed bracket are reused.
The PR #323 Banach exponential-flow equivalence is not re-proved or relabeled
as an unbounded modular-flow theorem.

| Owner | Exact construction or theorem | Dependencies |
|---|---|---|
| Core.TripotentIntegerGrading | Native graded monoid, internal direct sum, graded algebra and algebra equivalence for existing integer eigenspaces; support in [-2,2]; opposite-degree composites centralize S | Existing eigenspace and Peirce decomposition owners |
| PeirceSpine.TripotentIntegerSuperbracket | Actual sum-degree subtype brackets and one super-Jacobi equality for all three integer indices | Integer grades; existing associative super-Jacobi |
| Core.TripotentInvariantSubspaces | Existing five projectors equal native Lagrange polynomial aeval; every adjoint-invariant submodule has an internal decomposition; native Lie-subalgebra restriction | Native polynomial, eigenspace and direct-sum APIs |
| OperatorAlgebra.TripotentCornerActions | Square-zero corners; disjoint projector ranges; strict middle-range/kernel chain; exact individual dual kernels and their intersection | Actual endomorphism action and Peirce identities |
| OperatorAlgebra.TripotentExtremalJordanPair | Existing JordanPair bundle on L ∩ A±2, with constructed triple, double-commutator agreement, outer/fundamental identities and six shared linearity laws covering both signs | Homogeneous multiplication, native Lie closure and existing Jordan triple |
| Core.TripotentInvolution | Star and Krein grade transport; native ordinary skew Lie subalgebras; exact central-correction invariance; anticommutator obstruction | Native star modules and the owned Krein adjoint |
| Core.TripotentKreinBlocks | Projector exchange, reflected corner adjoint and reconstruction of actual skew elements in degrees zero and one | Existing projectors/eigenspaces and Krein involution |
| Core.TripotentOddGeneration | Real spans of odd anticommutators equal products of successive corner submodules; exact criterion for filling each extreme corner | Peirce orthogonality and native submodule multiplication |
| OperatorAlgebra.TripotentGradeTransport | Native algebra-automorphism covariance, unit conjugation, reversal, stationary transport and fixed-total-degree cancellation of composite generators | Existing grades, native ConjAct and component multiplication |
| Core.TripotentAdjointDefect | Native endomorphism identity D⁴ - D² = 12 • (Π₂ + Π₋₂), without a nonvanishing claim | Existing eigenpower evaluation and reconstruction |

Each row is a proof target until its exact source passes Lean. Source-semantic
review, compilation and axiom audit are different checks. No definition
assumes the desired construction as a witness field.

## Corrections required by the intake

1. The quintic is an annihilating polynomial. It need not be the minimal
   polynomial, and all five weights need not occur. The corrected defect is
   D⁴ - D² = D²(D² - I) = 12(Π₂ + Π₋₂); the extra factor 3 is incorrect.
2. For self-adjoint S, star reverses every grade, and each nonzero integer
   grade has zero intersection with the ordinary skew submodule. Skewness of
   S suffices for adjoint invariance, but is not a necessary classification.
   The exact condition is that S + star S centralize every skew element.
   The same correction holds for the stated Krein adjoint.
3. Ordinary skew elements are closed under commutators. Their anticommutator
   is self-adjoint and belongs to the skew space precisely when it is zero.
   A Krein involution therefore does not automatically produce odd-odd
   superclosure, nonzero extreme sectors, a particular conformal algebra,
   or a specified internal gauge algebra.
4. A single nonzero extreme operator cannot have kernel equal to the middle
   range. The equations N₊N₋ = P₊ and N₋N₊ = P₋ suffice for the intersection
   formula; they are not necessary for it.
5. Corner generation uses native submodule products and real spans: finite
   sums of ordered products. It does not assert surjectivity of a single
   anticommutator. Filling one extreme corner is not global Morita equivalence.
6. For inhomogeneous factors, cancellation concerns the sum of terms of each
   fixed nonzero total degree, not each individual product. A reversing unit
   reverses grades without having square one. The full normalizer of degree
   zero need not have only two components: even diagonal degree zero in M₃(ℝ)
   admits all permutation symmetries.
7. The bounded flow criterion uses differentiation and adjoint rigidity.
   Connectedness alone is not its proof. An unbounded Stone/resolvent theorem
   needs its domain, self-adjointness, spectral construction and strong
   topology. KMS additionally needs the specified state, dynamics and strip
   boundary condition. None follows from tripotence.
   If K = -log ρ, then exp(itK) = ρ^(-it); the opposite sign reverses time.
   A density with kernel requires restriction to its support for its densely
   defined logarithm.

## Analytic boundary

The bounded source search inspected pinned Mathlib
`Analysis/InnerProductSpace/LinearPMap.lean`, with partial adjoints, dense-domain
and closedness results for self-adjoint partial maps, and
`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean`, with bounded
continuous-functional-calculus commutation. The repository's
`KK/RealSplitKreinLinearResolventBridge.lean` supplies inverse and domain/range
identities for specified resolvent data. The inspected owners do not construct
an unbounded spectral measure or its unitary group from that resolvent.

Genuine bounded KMS analysis already exists in `ComplexTimeCorrelation.lean`
and `FilteredGNSMatrixAnalyticKMS.lean`. Those owners use actual complex-time
correlations, strip bounds, density/exponential compatibility and twisted
cyclicity. This is not an absence claim about all KMS machinery.

The remaining unbounded implication is the native construction and proof of

`[S,(i-K)⁻¹]=0 → [S,E_K(B)]=0 → [S,exp(itK)]=0`,

followed by invariance of a chosen smaller algebra and the state-specific KMS
boundary theorem. Bounded `cfc` at a discontinuous function on the resolvent
spectrum, or bounded `CFC.log` of a noninvertible density, cannot replace this
step. `commuting_unit_preserves_adGrade` supplies the subsequent algebraic
implication only after actual commutation has been established.

## Validation history and acceptance

- Independent source-semantic review accepted all ten candidates at their
  stated hypotheses; this is not kernel certification.
- Local exact-source attempts 1 and 2 copied closures of 40 and 56 repository
  modules respectively. Both stopped at the cache setup step with ENOSPC
  while creating the independent Mathlib `.lake/config` directory.
- Zero repository modules were compiled in those attempts; neither reached
  the declaration axiom audit. The environment subsequently became unavailable.
- The source snapshots were recovered byte-for-byte from retained tool output
  and independently reviewed snapshots. Each Lean owner's SHA256 was checked
  against its reviewed content. The intake hash and byte count also match.
- The focused remote workflow compiles the exact selected source closure and
  audits every declaration owned by the ten selected modules. Only the
  foundational axioms `propext`, `Classical.choice`, and `Quot.sound` are
  permitted. No root toolchain or dependency pin is changed.
- The first remote run, [43404383399](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43404383399),
  tested the tree of preservation commit
  `9ba1c218912ab8112d45aa03934abd4d72bc5d45` through PR merge
  `e160677928b34e11d5eb18b2278a5260e57adc4a`. It processed a closure of
  58 repository modules: 51 compiled, three failed, and four were blocked by
  those failures. The fail-closed checker did not perform a declaration audit.
- On that first run, the actual nonempty staged proof gate passed. Its changed
  Lean-source audit covered all ten owners and found zero proof gaps; the
  semantic-content, tracked-scope and quarantine checks also passed.
  The incremental root build stopped at the missing dependency
  `external_refs/homotopy-hypothesis-lean4`.
- The first step labelled as a full root gate omitted `--full` and therefore
  invoked the script's default incremental mode. It failed on shallow-history
  resolution of `HEAD~1`; it was not evidence of a full-mode attempt. The
  repaired workflow explicitly passes `--full`.
- Compiler repair commits preserve the theorem statements and hypotheses.
  Subsequent exact-source compilation, declaration-axiom results and root-gate
  outcomes are recorded separately in [PR #352](https://github.com/nickgou-nuke/info-geometry-lean/pull/352)
  and its immutable workflow runs. A focused result is not a whole-repository
  build certificate. Required root checks and unrelated blockers must be
  reported separately.

## Explicit interpretation limits

These algebraic constructions do not identify a canonical KKT Lie algebra
from tripotence alone. Horizon, infinity-twistor, supercolor, thermal-equilibrium
and physical-dynamics interpretations need further objects and compatibility
theorems. The unbounded resolvent/Stone/KMS extension remains a separate analytic
target; no assumption-only wrapper is presented as its construction.
